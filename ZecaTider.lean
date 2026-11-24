import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology

open Finset MeasureTheory Real
open scoped Classical

/-- future logarithmic growth. -/
def Amble (h:ℕ→ℝ) (C:ℝ) (n:ℕ) := ∀ i:ℕ, h (n+i) ≤ h n + C*i

/-- Low-mean-cost selection with future growth control. -/
lemma billow {h:ℕ→ℝ} {D m C : ℝ} (hm:0≤ m)(hc:8*m<C)
    (a:Monotone h) (b:∀ n,h n ≤ D+m*n):
   ∀ᶠ N:ℕ in atTop,∀ e:ℕ→ℝ,(∀ i,0≤e i) →
     ∃ i:ℕ, i ∈ range N ∧ Amble h C (N+i) ∧
         e i ≤ 4*((∑ i ∈ range N,e i)/N):=by
 let f(n):=h n-C*n
 let z(i:ℕ)(j:ℕ):=f (i+j)
 let w(i:ℕ):= ⨆ j,z i j
 have c0:0<C:=by linarith
 have h0(i j):z i j ≤ D+(m-C)*i:=by
   unfold z f
   have t:m-C≤0:= by linarith
   have l:= b (i+j)
   have q:=mul_nonpos_of_nonpos_of_nonneg t (Nat.cast_nonneg (α:=ℝ) j)
   push_cast at l ⊢
   linarith only [l,q]
        -- cast push needed

 have hz(i j): z i j ≤ w i:= by
   have u:BddAbove (Set.range (z i)):= by
      refine ⟨D+(m-C)*i,?_⟩; rintro x ⟨k,rfl⟩; exact h0 i k
   exact le_ciSup u j
 have hp(i): f i ≤ w i:=by simpa [z] using hz i 0
 have hn(i): w i ≤ D+(m-C)*i := ciSup_le (h0 i)
 have w0(i):w i ≤ max (f i) (w (i+1)):=by
   refine ciSup_le fun j=> ?_
   cases j with
   | zero=> simpa [z] using le_max_left (f i) (w (i+1))
   | succ j=>
     refine le_max_of_le_right ?_
     exact (show z i (j+1)=z (i+1) j from congrArg f (by omega)).le.trans (hz _ _)
 have wle(i):w i - w (i+1) ≤ C:=by
    have u : f i - C ≤ f (i+1):=by
      unfold f
      push_cast
      linarith only [a (Nat.le_succ i)]
    rcases le_max_iff.mp (w0 i) with t|t
    · linarith only [t,u,hp (i+1)]
    linarith only [t,c0]
 have wc(i)(p:w (i+1)<w i):Amble h C i:=by
    have t: w i ≤ f i:= (le_max_iff.mp (w0 i)).resolve_right p.not_ge
    intro j
    have l:= hz i j
    unfold z f at l

    unfold f at t
    push_cast at l
    linarith only [l,t]
 have k:= Filter.Tendsto.const_mul_atTop (show 0<C/10 by positivity) tendsto_natCast_atTop_atTop
 filter_upwards [eventually_gt_atTop 0,k.eventually_ge_atTop (D - h 0)]
    with N hn0 hcN e he
 have r:0<(N:ℝ):= Nat.cast_pos.mpr hn0
 have v:= mul_pos c0 r
 have price: C*N/2 < w N - w (N+N):=by
    have t:= hp N
    have u:= hn (N+N)
    push_cast at u
    unfold f at t
    linarith only [a (Nat.zero_le N),t,u,v,hcN, mul_lt_mul_of_pos_right hc r] 
 have drop: ∑ i ∈ range N,(w (N+i)-w (N+i+1)) = w N - w (N+N):=by
    have t(j:ℕ): ∑ i ∈ range j,(w (N+i)-w (N+i+1)) = w N - w (N+j):=by
       induction j with
       | zero=> simp
       | succ j ih =>
         rw [sum_range_succ,ih,add_assoc N j 1]; ring
    exact t _
 have pick:∃i∈range N, w (N+i+1)<w (N+i):=by
    by_contra! q
    have t: (∑ i ∈ range N,(w (N+i)-w (N+i+1))) ≤ 0:=
       Finset.sum_nonpos (fun i hi=> sub_nonpos.mpr (q i hi))
    rw [drop] at t; linarith only [v,price,t]
 let B:=(∑ i ∈ range N,e i)/N
 have bu: ∑ i ∈ range N,e i = B*N :=
      (div_mul_cancel₀ _ r.ne').symm
 have bpos:0≤B:= div_nonneg (sum_nonneg (fun _ _=>he _)) r.le
 rcases eq_or_lt_of_le bpos with bu0|bp
 · obtain ⟨i,hi,t⟩:=pick
   refine ⟨i,hi,wc _ t,?_⟩

   change _≤4*B
   apply le_trans (Finset.single_le_sum (f:=e) (fun j _=>he j) hi)
   calc
    _= B*N:=bu
    _=4*B:=by rw [←bu0,zero_mul,mul_zero]
    _≤_:=le_refl _
 by_contra! q
 have zq(i)(hi:i∈range N):
   (4*B)*(w (N+i)-w (N+i+1)) ≤ C*e i:=by
   rcases lt_or_ge (w (N+i+1)) (w (N+i)) with t|t
   · have u:4*B≤e i:=le_of_lt (q i hi (wc _ t))
     rw [mul_comm C]
     calc
        _≤ 4*B*C:=mul_le_mul_of_nonneg_left (wle _) (by positivity)
        _≤_:= mul_le_mul_of_nonneg_right u c0.le
   exact le_trans (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr t))
                (mul_nonneg c0.le (he i))
 have hu:= sum_le_sum zq
 rw [← Finset.mul_sum,drop, ←Finset.mul_sum] at hu
 have aux: C*(∑ i ∈ range N,e i) = C*(B*N):=congrArg (C*·) bu
 linarith only [mul_pos v bp,mul_lt_mul_of_pos_left price bp,aux,hu]
#print axioms billow

import ZecaLow
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S: OS.Semigroup H a)
local notation "R" => saucer S

variable (F:ℝ≥0→ℝ≥0→H.Op) (n:ℕ)
def sticks := ∀ t u:ℝ≥0,0<t→0<u→∀ s v,F (s+t) (u+v)=S.E s*F t u*S.E v
def mounts(d:ℕ)(b:ℝ):=∀ t:ℝ≥0,0<t→t≤1→‖F t t‖≤b/(t:ℝ)^d

structure Earn : Prop where
 power : ∃ d<n, ∃ b>0,mounts F d b
 con : sticks S F

def credit (D:H.Op): Prop:=∀ t u:ℝ≥0,0<t→0<u→
 S.E t * D * S.E u= R^n*F t u*R^n

def desk (t:ℝ≥0):=trade S n t*F t t*trade S n t

lemma deskDouble (c:sticks S F)(t:ℝ≥0)(h:0<t):
 desk S F n (t+t)=
 (trade S n (t+t)*S.E t) * F t t * (trade S n (t+t)*S.E t):=by
 unfold desk; rw [c t t h h t t]
 simp only [mul_assoc]
 rw [(trade_E S n t _).eq]


private lemma err_norm (A B X:H.Op){r d:ℝ}(h:‖A‖≤r)(p:‖B‖≤r)(m:‖A-B‖≤d):
 ‖A*X*A-B*X*B‖≤2*r*‖X‖*d:=by
 rw [show A*X*A-B*X*B=(A-B)*X*A+B*X*(A-B) by rw [sub_mul,sub_mul,mul_sub, sub_add_sub_cancel]]
 have k:0≤r:=(norm_nonneg _).trans h
 have z:0≤d:=(norm_nonneg _).trans m
 refine (norm_add_le ..).trans ((add_le_add (norm_mul_le ..) (norm_mul_le ..)).trans ?_)
 refine (add_le_add (mul_le_mul ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right m (norm_nonneg X)))
            h (norm_nonneg _) (by positivity)) (mul_le_mul ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right p (norm_nonneg X))) m (norm_nonneg _) (by positivity))).trans ?_
 ring_nf; rfl

lemma desk_diff (q:sticks S F){d:ℕ}(hd:d<n){b:ℝ}(p:0<b)
 (fee:mounts F d b)(t:ℝ≥0)(g:0<t)(u:t≤1):
  dist (desk S F n t) (desk S F n (t+t))≤
   2*(n*(2:ℝ)^n)^2*2^n*b*(t:ℝ):=by
 rw [deskDouble S _ _ q _ g,dist_eq_norm]
 refine (err_norm _ _ _ (trade_norm S t n) ((norm_mul_le ..).trans
    ((mul_le_of_le_one_right (norm_nonneg _) (S.shrinks _)).trans (trade_norm S _ n))) (trade_err S n t)).trans ?_
 rw [mul_pow 2 (t:ℝ)]
 have h:‖F t t‖ * (t:ℝ)^n ≤ b*t:= by
    apply (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one t.coe_nonneg (show (t:ℝ)≤1 from u) hd) (norm_nonneg _)).trans -- hd : d+1 ≤ n; ambiguity
    rw [pow_succ,←mul_assoc]
    exact mul_le_mul_of_nonneg_right
      ((le_div_iff₀ (pow_pos (show 0<(t:ℝ) from g) d)).mp (fee t g u)) t.coe_nonneg
 generalize (n:ℝ)*(2:ℝ)^n=r at *
 calc
   _ = 2*r^2*2^n*(‖F t t‖*(t:ℝ)^n):=by ring
   _ ≤ 2*r^2*2^n*(b*(t:ℝ)):=by gcongr
   _ = _:=by ring
def dy (i:ℕ):ℝ≥0:=(2⁻¹)^i
lemma dy_pos(i:ℕ):0<dy i:=by unfold dy; positivity
lemma dy_le(i:ℕ):dy i≤1:=pow_le_one₀ (by positivity) (by norm_num)
lemma dy_add (i:ℕ): dy (i+1)+dy (i+1)=dy i:=by
 apply NNReal.eq; simp [dy,pow_succ]; ring
lemma dy_go:Tendsto (fun i=>(dy i:ℝ)) atTop (𝓝 0):=by
 simp only [dy, NNReal.coe_pow,NNReal.coe_inv,NNReal.coe_ofNat]
 exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

lemma desk_go (q:Earn S F n): ∃ D,Tendsto (desk S F n ∘ dy) atTop (𝓝 D):=by
 obtain ⟨d,l,B,t,m⟩:=q.power
 let C:=2*((n:ℝ)*(2:ℝ)^n)^2*2^n*B
 apply cauchySeq_tendsto_of_complete
 refine cauchySeq_of_le_geometric (2⁻¹) (C*2⁻¹) (by norm_num) ?_
 intro i; rw [dist_comm]
 calc
   _ ≤ C*(dy (i+1):ℝ) :=by
        simpa only [dy_add i,C,Function.comp_apply] using desk_diff S F n q.con l t m _ (dy_pos (i+1)) (dy_le _)
   _= _ :=by rw [mul_assoc C,←pow_succ']; simp [dy]
lemma rec_exact (q:sticks S F)(u v t:ℝ≥0)(i:0<u)(r:0<v)(p:0<t):
   S.E u * desk S F n t * S.E v =
      (R^n - low S t ^ n) * F u v * (R^n - low S t ^ n):=by
 let A:=trade S n t
 have e:S.E u * A=A*S.E u:=(trade_E ..).eq
 have f:A*S.E v=S.E v*A:=(trade_E ..).symm.eq
 calc
   _=A*(S.E u * F t t * S.E v)* A:=by
       change S.E u*(A*_*A)*S.E v=_
       rw [←mul_assoc, ←mul_assoc, e]
       simp only [mul_assoc]
       rw [f]
   _=A*(S.E t * F u v * S.E t) * A:=by rw [←q _ _ p p, add_comm u t,add_comm t v,q _ _ i r]
   _=(A*S.E t)* F u v*(S.E t*A):=by simp only [mul_assoc]
   _=_:=by rw [show S.E t * A=A*S.E t from (trade_E ..).eq,
                show A*S.E t=_ from trade_price S n t]
lemma low_go:Tendsto (low S ∘ dy) atTop (𝓝 0):=
 tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _=> norm_nonneg _)
   (fun i=> low_norm S (dy i)) (by simpa using dy_go.const_mul 2)) -- fix
lemma earn_q (q:Earn S F n):∃ D,credit S F n D:=by
 obtain ⟨D,c⟩:=desk_go S F n q
 obtain ⟨d,p,-⟩:=q.power
 have e:n≠0:=by omega
 have m:Tendsto (fun i=>R^n-low S (dy i)^n) atTop (𝓝 (R^n)):= by
     simpa [e,Function.comp] using (((low_go S).pow n).const_sub (R^n))
 refine ⟨D,fun u v i r=> tendsto_nhds_unique_of_frequently_eq
     ((c.const_mul _).mul_const _) ((m.mul_const _).mul m) ?_⟩
 exact (Eventually.of_forall fun z=>rec_exact S F n q.con u v (dy z) i r (dy_pos _)).frequently
#print axioms earn_q
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca

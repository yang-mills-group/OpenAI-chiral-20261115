import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Velour.Damask.Panels
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Damask
open Function Set Filter Complex Metric Polynomial
open scoped Topology BigOperators Polynomial Classical

variable {n:ℕ}
local notation "ℓ"=> Fin n→ℝ
local notation "ℒ"=> Fin n→ℂ

def spindle (t u:ℝ)(z:ℂ) := cos z * t - sin z * u
def orbit (t u:ℝ)(z:ℂ) := sin z * t + cos z * u

def φ (t u:ℓ)(z:ℂ):ℒ:=fun i=> spindle (t i) (u i) z
def ψ (t u:ℓ)(z:ℂ):ℒ:=fun i=> orbit (t i) (u i) z

def wide (t u:ℝ)(x:ℝ):=Real.cos x*t-Real.sin x*u
def tall (t u:ℝ)(x:ℝ):=Real.sin x*t+Real.cos x*u
def rows (t u:ℓ)(x:ℝ):ℓ:= fun i=>wide (t i) (u i) x
def cols (t u:ℓ)(x:ℝ):ℓ:= fun i=>tall (t i) (u i) x
local notation "τ"=> (2*Real.pi)



lemma spun (t u:ℓ)(x:ℝ):
 φ t u x=(fun i=> (rows t u x i:ℂ)) ∧ ψ t u x=(fun i=>(cols t u x i:ℂ)):= by
 constructor <;> funext i <;> simp only [φ,spindle,rows, wide, cols,tall, ψ, orbit] <;>push_cast <;> rfl
lemma ran (t u:ℓ) (x:ℝ):
 rows t u (x+τ)=rows t u x ∧ cols t u (x+τ)=cols t u x:=by
 unfold rows cols wide tall
 rw [Real.sin_add_two_pi,Real.cos_add_two_pi]
 exact ⟨rfl,rfl⟩
lemma stood (t u:ℓ):rows t u 0=t:=by funext i; simp [rows,wide]

lemma wafts (t u:ℓ)(z:ℂ)(i:Fin n):
 AnalyticAt ℂ (fun x=>φ t u x i) z ∧ AnalyticAt ℂ (fun x=>ψ t u x i) z:=
 ⟨(analyticAt_cos.mul analyticAt_const).sub (analyticAt_sin.mul analyticAt_const),
  (analyticAt_sin.mul analyticAt_const).add (analyticAt_cos.mul analyticAt_const)⟩

private lemma divPlane (t u x y:ℝ):
 spindle t u (x+y*I) = (Real.cosh y:ℂ) * (wide t u x) - (Real.sinh y:ℂ)*(tall t u x)*I ∧
 orbit t u (x+y*I)=(Real.cosh y:ℂ)*(tall t u x) + (Real.sinh y:ℂ)*(wide t u x)*I:=by
 unfold spindle orbit wide tall; push_cast
 rw [cos_add,sin_add,cos_mul_I,sin_mul_I]
 constructor <;> ring

lemma wafts_four (t u:ℓ) (z:ℂ)(i:Fin n):
 (φ t u z i).re = Real.cosh z.im * rows t u z.re i ∧
 (ψ t u z i).im = Real.sinh z.im * rows t u z.re i ∧
 (ψ t u z i).re = Real.cosh z.im * cols t u z.re i ∧
 (φ t u z i).im = -(Real.sinh z.im * cols t u z.re i):=by
 have h:=divPlane (t i) (u i) z.re z.im
 rw [Complex.re_add_im] at h
 simp only [φ,ψ,rows,cols,h.1,h.2]
 simp [-ofReal_cosh,-ofReal_sinh]


lemma angular_price (x:ℝ):
 Real.exp |x| * (Real.cosh x - |Real.sinh x|)=1:= by
 rcases le_total 0 x with t|t
 · rw [abs_of_nonneg t, abs_of_nonneg (show 0≤Real.sinh x by 
        linarith [Real.cosh_sub_sinh x,Real.cosh_add_sinh x,
          Real.exp_le_exp.mpr (show -x≤x by linarith)]),
     Real.cosh_sub_sinh,← Real.exp_add,add_neg_cancel,Real.exp_zero]
 rw [abs_of_nonpos t, abs_of_nonpos (show Real.sinh x ≤0 by 
        linarith [Real.cosh_sub_sinh x,Real.cosh_add_sinh x,
          Real.exp_le_exp.mpr (show x≤ -x by linarith)]), sub_neg_eq_add,
     Real.cosh_add_sinh, ← Real.exp_add,neg_add_cancel,Real.exp_zero]

lemma row_bids (t u:ℓ)(z:ℂ)(i j:Fin n)(h:rows t u z.re i≤rows t u z.re j):
 Real.exp |z.im| *((φ t u z j - φ t u z i).re - |(ψ t u z j-ψ t u z i).im|)=
   rows t u z.re j-rows t u z.re i:=by
 rw [sub_re,sub_im,(wafts_four t u z j).1,(wafts_four t u z i).1,(wafts_four t u z j).2.1,(wafts_four t u z i).2.1]
 rw [←mul_sub,←mul_sub,abs_mul,abs_of_nonneg (sub_nonneg.mpr h),
     ←sub_mul,←mul_assoc,angular_price,one_mul]

lemma col_bids (t u:ℓ)(z:ℂ)(i j:Fin n)(h:cols t u z.re i≤cols t u z.re j):
 Real.exp |z.im| *((ψ t u z j - ψ t u z i).re - |(φ t u z j-φ t u z i).im|)=
   cols t u z.re j-cols t u z.re i:=by
 rw [sub_re,sub_im,(wafts_four t u z j).2.2.1,(wafts_four t u z i).2.2.1,(wafts_four t u z j).2.2.2,(wafts_four t u z i).2.2.2]
 rw [←neg_sub',abs_neg,←mul_sub,←mul_sub,abs_mul,abs_of_nonneg (sub_nonneg.mpr h),
     ←sub_mul,←mul_assoc,angular_price,one_mul]



def Oblique (t u:ℓ):Prop:=
 ∀i j k l,i≠j→k≠l→(t j-t i)*(t l-t k)+(u j-u i)*(u l-u k)≠0

-- Eventual in one scalar perturb y→ q y as q→1 strictly from above.
lemma open_row (t u:ℓ)(p:Injective t):
 ∀ᶠ r:ℝ in 𝓝[>] 1, Oblique t (fun i=>r*u i):=by
 refine eventually_all.mpr fun i=> eventually_all.mpr fun j=>eventually_all.mpr fun k=>
   eventually_all.mpr fun l=>eventually_all.mpr fun h=>eventually_all.mpr fun v=>?_
 let b:=(t j-t i)*(t l-t k)
 let d:=(u j-u i)*(u l-u k)
 let f(r:ℝ):=b+r^2*d
 have e(r:ℝ): b + (r*u j-r*u i)*(r*u l-r*u k)=f r:=by dsimp only [f,d];ring
 by_cases w:f 1=0
 · have g:b≠0:=mul_ne_zero (sub_ne_zero.mpr (p.ne h.symm)) (sub_ne_zero.mpr (p.ne v.symm))
   refine eventually_mem_nhdsWithin.mono fun r y q=>?_
   have z:f r=0:= (e r).symm.trans q
   dsimp only [f] at z w
   rw [one_pow, one_mul] at w
   have X:(r^2-1) * d=0:= by rw [sub_mul,one_mul]; linarith
   have k:1<r:=y
   have t:d≠0:=by intro x;rw [x,add_zero] at w; exact g w
   exact (mul_ne_zero (by nlinarith : r^2-1≠0) t) X


 have y:Continuous f:=by unfold f;fun_prop
 exact (((y.tendsto 1).eventually (isOpen_ne.mem_nhds w)).filter_mono nhdsWithin_le_nhds).mono
    fun r z q=>z ((e r).symm.trans q)

lemma slopes (t u:ℓ)(v:Oblique t u)(x:ℝ):
 Injective (rows t u x) ∨ Injective (cols t u x):=by
 by_contra z
 unfold Injective at z
 push Not at z
 obtain ⟨⟨i,j,g,h⟩,⟨k,l,e,w⟩⟩:=z
 apply v i j k l h w
 let T:=rows t u x; let U:=cols t u x
 rw [show (t j - t i)*(t l - t k)+(u j-u i)*(u l-u k)=
      (T j -T i)*(T l-T k)+(U j-U i)*(U l-U k) from by
       dsimp only [T,U,rows,cols,tall,wide]
       linear_combination -( (t j-t i)*(t l-t k)+(u j-u i)*(u l-u k)) * Real.sin_sq_add_cos_sq x,
     show T i=T j from g, show U k=U l from e,sub_self,sub_self,mul_zero,zero_mul,zero_add]

lemma permuting {t:ℓ}(p:Injective t):
 ∃g:Equiv.Perm (Fin n), StrictMono (t∘g):=by
 let s:=Finset.univ.image t
 let v:Fin n→s:= fun i=>⟨t i, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
 have e:Bijective v:= ⟨fun _ _ q=>p (congrArg Subtype.val q),
    fun i=>by
      obtain ⟨a,_,u⟩:=Finset.mem_image.mp i.property
      exact ⟨a,Subtype.ext u⟩⟩
 have c:s.card=n:=(Finset.card_image_of_injective _ p).trans (by simp)
 let f:=s.orderIsoOfFin c
 let h:=Equiv.ofBijective v e
 refine ⟨f.toEquiv.trans h.symm, fun i j p=>?_⟩
 change (h (h.symm (f i))).val<(h (h.symm (f j))).val
 rw [h.apply_symm_apply,h.apply_symm_apply]
 exact f.strictMono p

#print axioms slopes

def ladder (t:ℓ)(d:ℝ):Prop:=∀i j,i<j→d < t j - t i
lemma ladders {T:ℝ→ℓ}{x:ℝ}(p:StrictMono (T x))(c:∀i,ContinuousAt (fun y=>T y i) x):
 ∃d:ℝ,0<d ∧ ∀ᶠ y in 𝓝 x, ladder (T y) d:=by
 have e:∀ᶠ d in 𝓝[>] (0:ℝ), ladder (T x) d :=
    eventually_all.mpr fun _=>eventually_all.mpr fun _=>
      eventually_all.mpr fun h=> (eventually_lt_nhds (sub_pos.mpr (p h))).filter_mono nhdsWithin_le_nhds
 obtain ⟨d,u,v⟩:=(eventually_mem_nhdsWithin.and e).exists
 exact ⟨_,u, eventually_all.mpr fun i=>eventually_all.mpr fun j=>
      eventually_all.mpr fun h=> ((c j).sub (c i)).eventually (lt_mem_nhds (v _ _ h))⟩

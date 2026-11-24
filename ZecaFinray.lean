import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology



def fstroke(h:ℝ)(f:ℝ→ℂ):ℕ→ℝ→ℂ
 | 0 => f
 | n+1=> fun x => fstroke h f n (x+h)-fstroke h f n x

lemma strokeDeriv (h:ℝ) (f g:ℝ→ℂ)
 (d:∀x,HasDerivAt f (g x) x) (n:ℕ) (x:ℝ) :
 HasDerivAt (fstroke h f n) (fstroke h g n x) x:=by
 induction n generalizing x with
 | zero=> exact d x
 | succ k a =>
    have hv:= (a (x+h)).scomp x ((hasDerivAt_id' x).add_const h)
    rw [one_smul] at hv
    exact hv.sub (a x)

lemma strokePrice (h:ℝ)(hp:0≤h)(f:ℕ→ℝ→ℂ)
 (d:∀k x,HasDerivAt (f k) (f (k+1) x) x) (n:ℕ) (x:ℝ)
 (k:ℕ) {B:ℝ} (e:∀x,‖f (k+n) x‖≤B) :
 ‖fstroke h (f k) n x‖ ≤ B*h^n:=by
 induction n generalizing x k with
 | zero=>simpa [fstroke] using e x
 | succ m a =>
    have H(y:ℝ):‖fstroke h (f (k+1)) m y‖≤B*h^m:=
     a y _ (by rwa [show k+1+m=k+(m+1) from by omega])
    rw [fstroke,pow_succ,← mul_assoc]
    have v:= (convex_univ (𝕜:=ℝ) (E:=ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y _=>(strokeDeriv _ (f k) (f (k+1)) (d k) m y).hasDerivWithinAt)
      (fun y _=>H y)
      (mem_univ x) (mem_univ (x+h))
    simpa [Real.norm_eq_abs,abs_of_nonneg hp] using v
lemma paintDrivs (f:ℂ→ℂ) (x:ℂ)
    (h:AnalyticAt ℂ f x)(n:ℕ):
    AnalyticAt ℂ (iteratedDeriv n f) x:=by
 induction n with
 | zero => rwa [iteratedDeriv_zero]
 | succ n k=>rw [iteratedDeriv_succ];exact k.deriv
def fishNet(f:ℂ→ℂ)(R D:ℝ):Prop:=
  0 < R ∧ ∀x:ℝ,
  DiffContOnCl ℂ f (ball x R) ∧ ∀z∈sphere (x:ℂ) R,‖f z‖ ≤D
#check @iteratedDeriv_zero
lemma finray (h:ℝ) (hp:0≤h) (f:ℂ→ℂ) (R D:ℝ)
 (d:fishNet f R D)(n:ℕ) (x:ℝ):
 ‖fstroke h (fun y=>f y) n x‖ ≤
   n.factorial*D/R^n*h^n:=by
 have v(y:ℝ):AnalyticAt ℂ f y:=
   (d.2 y).1.1.analyticOnNhd Metric.isOpen_ball _ (mem_ball_self d.1)
 rw [← iteratedDeriv_zero (f:=f) (𝕜:=ℂ)]
 refine strokePrice _ hp
   (fun k y=> iteratedDeriv k f y) ?_ _ _ 0 (fun y=>?_ )
 · intro k y
   rw [iteratedDeriv_succ]
   exact (paintDrivs _ _ (v y) k).differentiableAt.hasDerivAt.comp_ofReal
 · rw [zero_add]
   exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le _
     d.1 (d.2 y).1 (d.2 y).2
#print axioms finray

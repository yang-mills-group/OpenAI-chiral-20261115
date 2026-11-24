import YM.SU5.Assay.Spacers
set_option autoImplicit false
noncomputable section
namespace YM.OS.Semigroup
open Set Metric Filter
open scoped Topology NNReal InnerProductSpace
variable {H:Hilbert}{j:Axis}(S:Semigroup H j)
local notation "ω"=>S.wax
/-! Positive lag modulus uniform for all election rooms. -/
variable {a b c:ℝ}
lemma wax_deriv (h:0<a):HasDerivAt S.wax (deriv S.F (↑a)) a:=by
 let C:ℝ→L[ℝ]ℂ:= Complex.ofRealCLM
 have t:C a∈inside:=h
 have y:=(((S.localHeat (C a) t).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt a
    (C.hasFDerivAt.hasDerivAt))
 change HasDerivAt _ ((fderiv ℂ S.F (↑a)) 1) a at y
 rw [fderiv_apply_one_eq_deriv] at y
 refine y.congr_of_eventuallyEq ?_
 filter_upwards [lt_mem_nhds h] with x u
 exact ((congrArg S.F (show C x = duration x.toNNReal from (congrArg ((↑):ℝ→ℂ) (Real.coe_toNNReal x u.le)).symm)).trans (S.roots_heat (Real.toNNReal_pos.mpr u))).symm
lemma wax_slow (h:0<a):‖deriv S.wax a‖≤2/a:=by
 rw [(S.wax_deriv h).deriv,show 2/a=1/(a/2) by ring]
 have y(z:ℂ)(v:z∈closedBall (↑a:ℂ) (a/2)):z∈inside:=by
    rw [mem_closedBall,dist_comm,dist_eq_norm] at v
    have p:=(Complex.re_le_norm _).trans v; rw [Complex.sub_re,Complex.ofReal_re] at p
    change 0<z.re
    linarith
 refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (half_pos h) ⟨?_,?_⟩ fun z v=> S.norm_row (y _ (sphere_subset_closedBall v))
 · intro z v
   exact (S.localHeat _ (y _ (ball_subset_closedBall v))).differentiableAt.differentiableWithinAt
 · intro z v
   exact (S.localHeat _ (y _ (closure_ball_subset_closedBall v))).continuousAt.continuousWithinAt
lemma wax_shaking (u:0<c)(w:c≤a)(q:c≤b):‖ω a-ω b‖≤2/c*‖a-b‖:=by
 refine Convex.norm_image_sub_le_of_norm_deriv_le (s:=Ici c) ?_ ?_ (convex_Ici _) q w
 · intro x v;exact (S.wax_analytic (u.trans_le v)).differentiableAt
 · intro x v;exact (S.wax_slow (u.trans_le v)).trans (div_le_div_of_nonneg_left zero_le_two u v)
variable {I:Type*}{l:Filter I}{f:I→ℝ}{e:ℝ}
lemma wax_mod (p:Tendsto f l (𝓝 b))(w:0<b)(q:0<e):∀ᶠ i in l,∀{H:Hilbert}{j:Axis}(S:Semigroup H j),‖S.wax (f i)-S.wax b‖<e:=by
 let c:=b/2; have h:0<c:=half_pos w; have t:c<b:=half_lt_self w
 have u:= (tendsto_iff_norm_sub_tendsto_zero.mp p).const_mul (2/c);rw [mul_zero] at u
 filter_upwards [u.eventually (gt_mem_nhds q),p.eventually (lt_mem_nhds t)] with i v y
 intro H j S; exact (S.wax_shaking h y.le t.le).trans_lt v
end YM.OS.Semigroup

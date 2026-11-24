import YM.Heat.Imaginary
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
/-!
# Spending the left-over heat

 One (polynomial, not exponential) energy weight on each of the actual views.
 Use only OS heat calculus; in particular no cone condition yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S: OS.Semigroup H a)(x y:H)(t:ℝ)(u:ℝ≥0)
scoped instance realH (H:Hilbert) : NormedSpace ℝ H:= NormedSpace.restrictScalars ℝ ℂ H.space
scoped instance towerH (H:Hilbert):IsScalarTower ℝ ℂ H.space:= IsScalarTower.restrictScalars ℝ ℂ H.space
abbrev highlande (t:ℝ):H.Op:= S.E t.toNNReal
def cups (t:ℝ):= Real.exp (-t) • highlande S t x
lemma stayPay (t:ℝ) : ‖highlande S t x‖≤‖x‖:= ((highlande S t).le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _))
lemma cupsP : ‖cups S x t‖ ≤ Real.exp (-t)*‖x‖ := by unfold cups; rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]; exact mul_le_mul_of_nonneg_left (stayPay S x t) (Real.exp_pos _).le
lemma cupsC : Continuous (cups S x) := (Real.continuous_exp.comp continuous_id.neg).smul ((S.continuousE x).comp continuous_real_toNNReal)
local notation "rayA"=> Ioi (0:ℝ)
lemma cupsI : IntegrableOn (cups S x) rayA:= ((integrableOn_exp_neg_Ioi 0).mul_const ‖x‖).mono' (cupsC ..).aestronglyMeasurable (Eventually.of_forall fun t=> cupsP S x t)
def ship := ∫ t in rayA, cups S x t
lemma ship_cost : ‖ship S x‖ ≤ ‖x‖ := by
 refine le_trans (norm_integral_le_of_norm_le ((integrableOn_exp_neg_Ioi 0).mul_const ‖x‖) (Eventually.of_forall fun t => cupsP S x t)) ?_; rw [integral_mul_const,integral_exp_neg_Ioi_zero,one_mul]
def saucerL : H →ₗ[ℂ] H where
 toFun:=ship S
 map_add' x y:=by change (∫ t in rayA, _)=_; unfold cups; simp_rw [map_add,smul_add]; exact integral_add (cupsI S x) (cupsI S y)
 map_smul' c x:=by change (∫ t in rayA, _)= c • _; unfold cups; simp_rw [map_smul,smul_comm (Real.exp _) c]; exact integral_smul ..
def saucer : H.Op:= (saucerL S).mkContinuous 1 (fun x=>by rw [one_mul]; exact ship_cost S x) 
lemma saucer_apply : saucer S x= ship S x:= rfl
lemma pot : ‖saucer S‖≤1:=ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun x=>by rw [one_mul]; exact ship_cost S x)
#print axioms pot
-- Center
variable (A : H.Op)(v:Cross a)(z:ℂ)
lemma ship_left (p:∀ u,Commute (S.E u) A) : Commute (saucer S) A := by
 change saucer S*A=A*saucer S; ext1 x; change ship S (A x) = A (ship S x); unfold ship; rw [← A.integral_comp_comm (cupsI S x)]; congr 1 with t; unfold cups; rw [(show highlande S t (A x)=_ from congrArg (fun f:H.Op=> f x) (p _).eq), A.map_smul_of_tower]; rfl
lemma still (h:∀ t,S.E t x=x): saucer S x=x:= by rw [saucer_apply]; unfold ship cups highlande; simp_rw [h]; rw [integral_smul_const,integral_exp_neg_Ioi_zero,one_smul]
lemma cupE : Commute (saucer S) (S.E u):= ship_left S _ fun s=>(S.time s u |>.symm).trans ((congrArg S.E (add_comm s u)).trans (S.time u s))
lemma cupU : Commute (saucer S) (S.U v):= ship_left S _ fun s=>S.independent s _
lemma CBurner : Commute (S.E u) (S.edge t) := by
 rcases eq_zero_or_pos u with rfl|h; · rw [S.eZero]; exact Commute.one_left _
 rw [← S.roots_heat h]; exact (S.either (dur.mpr h) t).trans (S.along (dur.mpr h) t).symm
lemma cupL : Commute (saucer S) (S.edge t):= ship_left S _ fun s=> CBurner S t s
lemma cupF (h:z∈inside): Commute (saucer S) (S.F z):= ship_left S _ fun s=> by
 rcases eq_zero_or_pos s with rfl|g; · rw [S.eZero]; exact Commute.one_left _
 rw [← S.roots_heat g]; exact (S.pairs (dur.mpr g) h|>.symm).trans ((congrArg S.F (add_comm ..)).trans (S.pairs h (dur.mpr g)))
private lemma mis (t:ℝ): inner ℂ x (cups S y t)=inner ℂ (cups S x t) y:=by
 change inner ℂ x ((Real.exp (-t):ℂ) • _) = inner ℂ ((Real.exp (-t):ℂ) • _) y; rw [inner_smul_left,inner_smul_right]; rw [conj_ofReal]; exact congrArg ((↑(Real.exp (-t)):ℂ) * ·) (by simpa only [S.sym] using ContinuousLinearMap.adjoint_inner_right (S.E t.toNNReal) x y)
lemma saucer_sym : IsSelfAdjoint (saucer S) := by
 let F:= saucer S; change F.adjoint=F; ext1 y; apply ext_inner_left ℂ; intro x; rw [ContinuousLinearMap.adjoint_inner_right]; change inner ℂ (ship S x) y= inner ℂ x (ship S y); unfold ship; rw [←inner_conj_symm, ← integral_inner (cupsI S x), ← integral_inner (cupsI S y), ← integral_conj]; congr 1 with t; rw [inner_conj_symm, mis]
#print axioms saucer_sym
end YM.CF.Buffered.Afterglow.Hierarchy.Seld

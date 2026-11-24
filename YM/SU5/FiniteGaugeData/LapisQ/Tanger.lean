import YM.SU5.FiniteGaugeData.Lapis.Eclipse
/-! # WP22B. Curvature probes. Angular Gaussian tuition stamps. Diagonal relation free comet.
Real cost. -/
set_option autoImplicit false
set_option maxHeartbeats 480000
set_option synthInstance.maxSize 23000
noncomputable section
namespace YM.SU5.FiniteGaugeData.LapisQ
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix Real
open Lapis Lapis.Motif WithLp
open scoped Topology RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Classical
set_option quotPrecheck false
namespace Apoth
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ι:Type}[Fintype ι] [DecidableEq ι] {a y v:ℝ}
noncomputable abbrev coatF(x:ℝ): ℝ:= Real.exp (-x^2/4)
lemma coat_p (x:ℝ):0<coatF x:=Real.exp_pos _
lemma coat_high(x:ℝ):coatF x≤1:=Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by norm_num))
local notation "μ"=> gaussianReal 0 1
noncomputable def peso (x:ℝ):=(Real.sqrt (1+x/2))⁻¹
#check integral_gaussianReal_eq_integral_smul
lemma lotion(a:ℝ) : (∫ x, coatF (a*x) ∂gaussianReal 0 1) = peso (a^2):=by
 rw [integral_gaussianReal_eq_integral_smul (by norm_num: (1:ℝ≥0) ≠ 0)]
 let r:=1+(a^2)/2; let c:= (√(2* π))⁻¹; have hp:0<r:=by unfold r; positivity
 have he(x:ℝ) : gaussianPDFReal 0 1 x • coatF (a*x)= c* Real.exp (- (r/2) *x^2):=by
    unfold gaussianPDFReal coatF c; rw [smul_eq_mul]; norm_num; rw [mul_assoc,← Real.exp_add]; congr 2; unfold r; ring -- tune smul
 simp_rw [he]; rw [integral_const_mul,integral_gaussian]
 unfold peso; change (√(2*π))⁻¹*√(π/(r/2)) =(√ r)⁻¹
 rw [show π/(r/2)=2*π*(r⁻¹) from (by field_simp), Real.sqrt_mul (by positivity : 0 ≤ 2*π), sqrt_inv, ←mul_assoc, inv_mul_cancel₀ (by positivity),one_mul]
-- panel of probes.h_Color.Price.
variable (A:ι→E)
local notation "V"=> EuclideanSpace ℝ ι
local notation "P₀" x:max=> stdGaussian x
local notation "T"=>EuclideanSpace ℝ
-- map using sum
noncomputable def opus (A:ι→ E) : E→L[ℝ] EuclideanSpace ℝ ι:= LinearMap.toContinuousLinearMap {
  toFun:= fun x=> toLp 2 (fun i=> inner ℝ (A i) x)
  map_add':= fun x y=> by ext; simp [inner_add_right]
  map_smul':= fun x y=> by ext; simp [real_inner_smul_right]
}
noncomputable def vista(A:ι→E): EuclideanSpace ℝ ι→L[ℝ] EuclideanSpace ℝ ι:= LinearMap.toContinuousLinearMap { toFun:= fun x :EuclideanSpace ℝ ι=>toLp 2 (fun i=>‖A i‖*x i), map_add' x y:= by ext; simp [mul_add], map_smul' c x:= by ext; simp [mul_left_comm] }
def sepOpt := ∀ i j:ι,i≠j→inner ℝ (A i) (A j)=0
lemma panel (a:V): (opus A).adjoint a = ∑ i:ι, a i • A i:=by
 apply ext_inner_right ℝ; intro b; rw [ContinuousLinearMap.adjoint_inner_left (opus A), sum_inner, EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct]
 apply sum_congr rfl; intro i _; rw [real_inner_smul_left]; exact mul_comm _ _
lemma v_panel(a:V): (vista A).adjoint a=vista A a:=by
 apply ext_inner_right ℝ; intro b; rw [ContinuousLinearMap.adjoint_inner_left (vista A), EuclideanSpace.inner_eq_star_dotProduct,EuclideanSpace.inner_eq_star_dotProduct,star_trivial,star_trivial]; refine sum_congr rfl fun i _=>?_ ; change ‖A i‖ * b i * a i= b i*(‖A i‖ * a i); ring
variable (p:sepOpt A)
include p
lemma rimC(a:V): ‖(opus A).adjoint a‖=‖(vista A).adjoint a‖:=by
 suffices he: ‖(opus A).adjoint a‖^2=‖(vista A).adjoint a‖^2 by nlinarith only [he,norm_nonneg ((opus A).adjoint a), norm_nonneg ((vista A).adjoint a)] -- tune
 rw [panel,v_panel,EuclideanSpace.real_norm_sq_eq, ← real_inner_self_eq_norm_sq,sum_inner]; apply sum_congr rfl; intro i _; rw [inner_sum,sum_eq_single i]; · rw [real_inner_self_eq_norm_sq,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]; change _=(‖A i‖*a i)^2; ring
 · intro j t y; rw [real_inner_smul_right,real_inner_smul_left,p i j y.symm,mul_zero,mul_zero]
 simp
lemma cook : Measure.map (opus A) (stdGaussian E)= Measure.map (vista A) (stdGaussian (EuclideanSpace ℝ ι)):=by
 apply Measure.ext_of_charFun; ext a; rw [dusk,dusk,charFun_stdGaussian,charFun_stdGaussian,rimC A p]
#check integral_fintype_prod_eq_prod
lemma probate : (∫ u:E,(∏ i:ι,coatF (inner ℝ (A i) u)) ∂ stdGaussian E)= ∏ i:ι,peso (‖A i‖^2):=by
 let f(x:V):=∏ i:ι,coatF (x i); have he: Measurable f:=(show Continuous f by unfold f coatF; fun_prop).measurable
 let P:=stdGaussian E; let l:= (Measure.pi (fun _ :ι=>gaussianReal 0 1)); change (∫ u,f (opus A u) ∂stdGaussian E)=_; rw [←integral_map (opus A).continuous.aemeasurable he.aestronglyMeasurable,cook A p,integral_map (vista A).continuous.aemeasurable he.aestronglyMeasurable,← map_pi_eq_stdGaussian]; change (∫ x: EuclideanSpace ℝ ι, (f ∘ vista A) x∂l.map (toLp 2))=_; rw [integral_map (by fun_prop : AEMeasurable (toLp 2) l) (he.comp (vista A).continuous.measurable).aestronglyMeasurable]
 change ∫ u:(ι→ℝ), (∏ i:ι, coatF (‖A i‖ * u i)) ∂l =_
 unfold l; rw [integral_fintype_prod_eq_prod (E:=fun _=>ℝ) (fun i:ι=> fun x:ℝ=> coatF (‖A i‖*x))]; simp_rw [lotion]
end Apoth
end YM.SU5.FiniteGaugeData.LapisQ
#print axioms YM.SU5.FiniteGaugeData.LapisQ.Apoth.probate

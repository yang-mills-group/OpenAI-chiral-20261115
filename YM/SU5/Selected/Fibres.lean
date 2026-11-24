import YM.SU5.Selected.Averages
/-!
# State and GNS tools and a characterization of extremality for joint rank-one vacua

Only need the sufficiency direction. Use a joint functional (concord) not assumed selfadjoint,
whose contraction means project to the joint ground. This extremality criterion is
among *all* `VacuumStates` of B, not simply relative to the compressed integral or among its
characters. Precise stationarity used here: vacuum fixed in the GNS construction by every b.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.SelectionAnalysis
open Function Filter Topology Set Metric Finset UniformSpace
open scoped Topology InnerProductSpace NNReal ENNReal ComplexOrder ComplexConjugate CStarAlgebra

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (f : B →ₚ[ℂ] ℂ)
local notation "H" f:max => PositiveLinearMap.GNS f
local notation "Π" f:max => PositiveLinearMap.gnsStarAlgHom f
open PositiveLinearMap

/-- the embedded B letter. -/
def appear (x : B) : f.GNS := (f.toPreGNS x:f.PreGNS)
lemma fibre_pair (x y : B) : inner ℂ (appear f x) (appear f y) = f (star x*y) := by
  rw [appear,appear,Completion.inner_coe]; exact preGNS_inner_def ..
lemma fibre_mul (x y : B) : (Π f) x (appear f y)=appear f (x*y) := by
  change f.gnsNonUnitalStarAlgHom x _=_; unfold appear; rw [gnsNonUnitalStarAlgHom_apply_coe]; exact congrArg (fun x : f.PreGNS => (x:f.GNS)) (by simp) -- type projection
lemma fibre_dense : DenseRange (appear f) := by
  apply (@Completion.denseRange_coe f.PreGNS _).mono
  rintro _ ⟨x,rfl⟩; exact ⟨f.ofPreGNS x,rfl⟩
local notation "a" => appear f 1
lemma fibre_vec (x : B) : appear f x=f.gnsStarAlgHom x a := by rw [fibre_mul,mul_one]
lemma fibre_cont : Continuous (appear f) := by
  have h : Continuous (f.gnsStarAlgHom) := map_continuous _
  have hx : appear f=(fun x => (Π f) x a) := funext (fibre_vec f)
  rw [hx]; exact (ContinuousLinearMap.apply ℂ f.GNS a).continuous.comp h
lemma fibre_mean (x : B) : inner ℂ a ((Π f) x a)=f x := by rw [fibre_mul, fibre_pair,star_one,mul_one,one_mul]
lemma fibre_norm (x : B) : Complex.re (f (star x*x))=‖appear f x‖^2 := by
  rw [← fibre_pair]; exact inner_self_eq_norm_sq (𝕜:=ℂ) _
lemma fibre_vacuum (h : f 1=1) : ‖a‖=1 := by
  have hv := fibre_norm f 1; rw [star_one,one_mul,h,Complex.one_re] at hv
  nlinarith [norm_nonneg a]
lemma fibre_first (x : B) : inner ℂ a (appear f x) = f x := by rw [fibre_pair,star_one,one_mul]
lemma fibre_cell (x : B) (z : ℂ) : appear f (x-z • 1)=appear f x-z • a := by
  unfold appear; rw [map_sub, map_smul, Completion.coe_sub,Completion.coe_smul]

local notation "A" f:max x:max => appear f x
variable (b : ℕ → B) (p : ∀ i, ‖b i‖ ≤ 1)
local notation "R" f:max => joint b (Π f)
local notation "P" f:max => (R f).orthogonalProjectionOnto
local notation "L" f:max => (R f).starProjection

/-- Convex criterion on positive linear functionals. No ordinary probability or *
in the Euclidean algebra required. B is an operator C*-algebra. -/
structure VacuumState : Prop where
  unit_norm : f 1=1
  fixes_vacuum (i : ℕ) : f (b i)=1
include p
lemma VacuumState.stationary (h : VacuumState f b) (i) : f.gnsStarAlgHom (b i) a=a := by
  let x := f.gnsStarAlgHom (b i)
  apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜:=ℂ)
  · apply (ContinuousLinearMap.le_opNorm x a).trans
    exact mul_le_of_le_one_left (norm_nonneg _) ((NonUnitalStarAlgHom.norm_apply_le ..).trans (p i))
  rw [inner_re_symm (x a) a,fibre_mean, h.fixes_vacuum,fibre_vacuum f h.unit_norm]; simp
lemma VacuumState.grounded (h : VacuumState f b) : a ∈ R f := (mem_joint b p (Π f) _).2 (h.stationary f b p)
lemma VacuumState.project_mean (h : VacuumState f b) (x : H f) :
    inner ℂ a ((L f) x) = inner ℂ a x := by rw [← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (h.grounded f b p)]

omit p in
def SingleGround : Prop := ∀ x : f.GNS, x ∈ joint b f.gnsStarAlgHom → ∃ z : ℂ, z • appear f 1=x
lemma projects (v : VacuumState f b) (w : SingleGround f b) (x : B) :
    (L f) (appear f x)= f x • a := by
  obtain ⟨c,h⟩ := w _ ((R f).starProjection_apply_mem (appear f x))
  rw [←h]; have hk := v.project_mean f b p (A f x); rw [←h,inner_smul_right,fibre_first,fibre_first, v.unit_norm,mul_one] at hk
  rw [hk]
omit p in
def ExtremeVacuum : Prop := VacuumState f b ∧
  ∀ g h : B →ₚ[ℂ] ℂ, VacuumState g b → VacuumState h b → ∀ w : ℝ,
    0 < w → w < 1 → (∀ x : B, f x=(w:ℂ)*g x + (1-(w:ℂ))*h x) → f=g ∧ f=h

private lemma dominated (v : VacuumState f b) (k : SingleGround f b) (g : B →ₚ[ℂ] ℂ)
    (u : VacuumState g b) {w : ℝ} (e : 0 < w) (h : ∀ x, w*‖appear g x‖^2 ≤ ‖appear f x‖^2) : f=g := by
  apply DFunLike.ext; intro x
  let y := x-f x • 1
  let C := probe (concord b)
  let z (f' : B →ₚ[ℂ] ℂ) (n) := appear f' (C n*y)
  have ht (f' : B →ₚ[ℂ] ℂ) : Tendsto (z f') atTop (𝓝 ((joint b f'.gnsStarAlgHom).starProjection (appear f' y))) := by
    have ht := emerges (Π f') (appear f' y) b p -- order
    unfold z
    simp_rw [←fibre_mul]
    exact ht
  have hx := ht f; rw [projects f b p v k, show f y=0 from (by unfold y; simp [v.unit_norm]), zero_smul] at hx
  have he := le_of_tendsto_of_tendsto' (((ht g).norm.pow 2).const_mul w) (hx.norm.pow 2) (fun i => h _)
  let j := (L g) (appear g y); change w*‖j‖^2 ≤ ‖(0:H f)‖^2 at he
  rw [norm_zero] at he
  have hsq : ‖j‖^2 ≤ 0 := by apply le_of_mul_le_mul_left _ e; rw [mul_zero]; norm_num at he; exact he
  have h₁ : j=0 := norm_eq_zero.mp (by nlinarith [norm_nonneg j])
  have hh := u.project_mean g b p (appear g y)
  rw [show (L g) _=0 from h₁, inner_zero_right,fibre_first] at hh
  exact (sub_eq_zero.mp (show g x-f x=0 from by simpa [y,u.unit_norm] using hh.symm)).symm

theorem single_is_extreme (v : VacuumState f b) (w : SingleGround f b) : ExtremeVacuum f b := by
  refine ⟨v,?_⟩
  intro g h k q rQ u e s
  have he := sub_pos.mpr e
  have hz (x : B) : ‖appear f x‖^2 = rQ * ‖appear g x‖^2 + (1-rQ) * ‖appear h x‖^2 := by
    rw [← fibre_norm, ← fibre_norm, ← fibre_norm,s]; simp [Complex.mul_re]
  refine ⟨dominated f b p v w g k u (fun x => ?_), dominated f b p v w h q he (fun x => ?_)⟩ <;> rw [hz];
  · exact le_add_of_nonneg_right (by positivity)
  exact le_add_of_nonneg_left (by positivity)

end YM.SelectionAnalysis
#print axioms YM.SelectionAnalysis.fibre_mul
#print axioms YM.SelectionAnalysis.projects
#print axioms YM.SelectionAnalysis.single_is_extreme

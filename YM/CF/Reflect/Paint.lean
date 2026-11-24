import YM.CF.Reflect.Cone
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! RP square for a finite crossing. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Reflect
open Fock Finset Function Filter NormedSpace MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology BoundedContinuousFunction ComplexOrder
attribute [local instance] opCStarAlgebra
section
variable {X Z : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X] [NormedAddCommGroup Z] [SecondCountableTopology Z]
lemma roof {μ : Measure X} [IsFiniteMeasure μ] {f : X → Z} (h : Continuous f) {r : ℝ} (p : ∀ i, ‖f i‖≤r) : Integrable f μ :=
  (integrable_const (c:=r)).mono' h.aestronglyMeasurable (Eventually.of_forall p) -- tune
end
variable {D n : Type*} [TopologicalSpace D] [MeasurableSpace D] [BorelSpace D] [SecondCountableTopology D] [LinearOrder n] [Fintype n] (U : UNI n) {S : Finset n}
variable (v : Finset n) (p : twist U (cutM vᶜ)=cutM v) (q : twist U (cutM S)=cutM Sᶜ) (μ : Measure D) [IsFiniteMeasure μ]
def factor (s : Finset n) (A : CSeat D n) := ∫ x:D×D,A x s s ∂μ.prod μ
lemma sized_entry {D : Type*} [TopologicalSpace D] [MeasurableSpace D] [BorelSpace D] {μ:Measure D} [IsFiniteMeasure μ] (A : CBox D n) (s t : Finset n) : Integrable (fun x:D=> A x s t) μ :=
  roof (A.continuous.matrix_elem s t) (fun i=> le_trans (norm_entry ..) (A.norm_coe_le_norm i))
lemma factor_pos (A : CSeat D n) (h : Faced U S A) : (p : twist U (cutM vᶜ)=cutM v) → (q : twist U (cutM S)=cutM Sᶜ) → 0≤factor μ v A := by
  intro p q
  induction h with
  | zero => simp [factor]
  | square b f L=>
    let g := fun x:D=> f x v v
    have he i : tile U b f i v v=star (g i.2)*g i.1 := theta_square v U p S q (f i.2) (f i.1) b (L _) (L _)
    unfold factor; rw [integral_prod (f:=fun i=>tile U b f i v v)]; simp_rw [he]
    ·
      simp_rw [integral_mul_const]; change 0 ≤ ∫ x:D,(∫ y:D, star (g y) ∂μ)*g x ∂μ
      rw [integral_const_mul,show (∫ y:D, star (g y) ∂μ)=star (∫ y:D,g y ∂μ) from integral_conj]; exact star_mul_self_nonneg _
    exact sized_entry ..
  | @plus f g a b ih it =>
    unfold factor; change 0 ≤ ∫ x,(f x+g x) v v ∂_; simp_rw [Matrix.add_apply]; rw [integral_add (sized_entry ..) (sized_entry ..)]; exact add_nonneg ih it
  | @raise t e f g ih=>
    unfold factor; change 0 ≤ ∫ x,(t • f x) v v ∂_; simp_rw [Matrix.smul_apply]; rw [integral_smul]; exact smul_nonneg e ih
lemma rehab (s : Finset n) : Continuous (factor μ s) := by
  let V : CSeat D n →ₗ[ℝ] ℂ :=
    { toFun := factor μ s
      map_add' := by
        intro f g; unfold factor; change (∫ x,(f x+g x) s s ∂_)=_; simp_rw [Matrix.add_apply]; exact integral_add (sized_entry ..) (sized_entry ..)
      map_smul' := by
        intro a f; unfold factor; change (∫ x, (a • f x) s s ∂_)= _; simp_rw [Matrix.smul_apply]; exact integral_smul .. }
  let c := (μ.prod μ).real Set.univ
  have he (x : CSeat D n) : ‖V x‖≤ c*‖x‖ := by
    unfold V; dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [mul_comm]; exact (norm_integral_le_of_norm_le_const (μ:=μ.prod μ) (C:=‖x‖) (f:=fun i=>x i s s) (Eventually.of_forall (fun i=> le_trans (norm_entry ..) (x.norm_coe_le_norm i)))) -- tune
  exact (V.mkContinuous c he).continuous
include p q
lemma cloud_pos {A : CSeat D n} (h : A ∈ Cloud U S D) : 0 ≤ factor μ v A := closure_minimal (fun x h=>factor_pos U v μ x h p q) (isClosed_le continuous_const (rehab ..)) h
end YM.CF.Reflect

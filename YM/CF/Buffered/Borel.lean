import YM.CF.Girt.Light

/-!
# Bounded Borel helpers

All costs in this file are at fixed finite geometry only.
-/

set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace RG Lattice MeasureTheory Finset Push.SectorMeasure
attribute [local instance] opCStarAlgebra
scoped instance (n : Type*) [Fintype n] [DecidableEq n] : MeasurableSpace (Op n) := borel _
scoped instance (n : Type*) [Fintype n] [DecidableEq n] : BorelSpace (Op n) := ⟨rfl⟩

section envelope
variable {X Y V Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace V] [MeasurableSpace Z]
  [NormedAddCommGroup V] [BorelSpace V]
  {f : X → V}
omit [BorelSpace V] in
lemma env_indicator (p : Set X) (hp : MeasurableSet p) (h : Envelope f) : Envelope (p.indicator f) := by
  obtain ⟨K,t⟩ := h.cost
  refine ⟨h.meas.indicator hp, max K 0, fun x => ?_⟩
  by_cases h : x ∈ p
  · rw [Set.indicator_of_mem h]; exact (t x).trans (le_max_left ..)
  rw [Set.indicator_of_notMem h, norm_zero]; exact le_max_right ..
lemma env_piece [TopologicalSpace X] [OpensMeasurableSpace X] (p : Set X) (hp : MeasurableSet p)
    (h : ContinuousOn f p) (K : ℝ) (w : ∀ x ∈ p, ‖f x‖ ≤ K) : Envelope (p.indicator f) := by
  classical
  refine ⟨?_, max K 0, fun x => ?_⟩
  · exact h.measurable_piecewise (show ContinuousOn _ pᶜ from continuousOn_const (c := (0:V))) hp
  by_cases H : x ∈ p
  · rw [Set.indicator_of_mem H]; exact (w x H).trans (le_max_left ..)
  rw [Set.indicator_of_notMem H, norm_zero]; exact le_max_right ..

variable [SecondCountableTopology V]
lemma env_marginal [NormedSpace ℝ V] {f : X × Y → V} (h : Envelope f) (μ : Measure Y) [IsProbabilityMeasure μ] :
    Envelope fun x => ∫ y, f (x,y) ∂μ := Env.marginal (g:=f ∘ Prod.swap) (Env.along h measurable_swap) _
end envelope

section
variable {X V : Type*} [MeasurableSpace X] [MeasurableSpace V] [NormedRing V]
variable [BorelSpace V] [SecondCountableTopology V] [ProperSpace V] {f g : X → V}
lemma env_mult (h : Envelope f) (p : Envelope g) : Envelope fun x => f x * g x :=
  Girt.kitE _ _ (· * ·) (by fun_prop) h p
end
end YM.CF.Buffered

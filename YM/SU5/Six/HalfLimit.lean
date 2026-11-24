import YM.Mink.Geometry
import YM.SU5.Six.WeakVary

/-!
# Costs on the frequency half-space, with a clamp extension

Allow dependence off `time ≥ 0` to be completely arbitrary (not
necessarily Borel), requiring measurability and bounds only on the closed
half-space itself, where the zoomed spectral measures are carried.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Six
open MeasureTheory Filter Set Metric
open scoped Topology

/-- Frequency half-space at `timeAxis = 3`. -/
def half : Set E4 := {p | 0 ≤ time p}
lemma half_closed : IsClosed half := isClosed_le continuous_const Mink.clock_cont

def gate (p : E4) : E4 := position (spatial p) (max 0 (time p))
@[fun_prop] lemma gate_cont : Continuous gate :=
  show Continuous (Mink.divide.symm ∘ (fun p => (spatial p, max 0 (time p)))) from by fun_prop
lemma gate_mem (p : E4) : gate p ∈ half := by
  exact show 0 ≤ time (gate p) by simp [gate]
lemma gate_id {p : E4} (h : p ∈ half) : gate p = p :=
  by rw [gate, max_eq_right (show 0 ≤ time p from h), position_eta]

structure HalfTest (f : E4 → ℂ) : Prop where
  borel : Measurable (half.restrict f)
  bounded : ∃ C : ℝ, ∀ p ∈ half, ‖f p‖ ≤ C

/-- The test hypothesis for the variable-function matrix zoom. -/
structure HalfLimit (F : ℕ → E4 → ℂ) (f : E4 → ℂ) : Prop where
  borel (i : ℕ) : Measurable (half.restrict (F i))
  bounded : ∃ C : ℝ, ∀ i p, p ∈ half → ‖F i p‖ ≤ C
  continuous : ContinuousOn f half
  converges (K) : IsCompact K → K ⊆ half → TendstoUniformlyOn F f atTop K

variable {f : E4 → ℂ} {F : ℕ → E4 → ℂ} {μ : Measure E4}

lemma HalfTest.clamp (h : HalfTest f) :
    Measurable (f ∘ gate) ∧ (∃ C : ℝ, ∀ p, ‖(f ∘ gate) p‖ ≤ C) := by
  obtain ⟨C,hC⟩ := h.bounded
  exact ⟨h.borel.comp (gate_cont.measurable.subtype_mk (h:=gate_mem)), C, fun p => hC _ (gate_mem p)⟩

lemma clamp_ae (k : ∀ᵐ p ∂μ, p ∈ half) : f ∘ gate =ᵐ[μ] f :=
  k.mono fun _ hp => congrArg f (gate_id hp)

lemma HalfTest.integrable [IsFiniteMeasure μ] (h : HalfTest f) (k : ∀ᵐ p ∂μ, p ∈ half) :
    Integrable f μ := by
  obtain ⟨hg,C,hC⟩ := h.clamp
  exact (Integrable.of_bound hg.aestronglyMeasurable C (ae_of_all _ hC)).congr (clamp_ae k)

namespace HalfLimit

lemma fixed (hf : ContinuousOn f half) (hb : ∃ C : ℝ, ∀ p ∈ half, ‖f p‖ ≤ C) :
    HalfLimit (fun _ => f) f := by
  obtain ⟨C,hC⟩ := hb
  refine ⟨fun _ => hf.restrict.measurable, ⟨C, fun _ => hC⟩, hf, ?_⟩
  exact fun _ _ _ => Metric.tendstoUniformlyOn_iff.mpr fun ε hε =>
    .of_forall fun _ _ _ => (dist_self _).trans_lt hε

lemma term (h : HalfLimit F f) (i : ℕ) : HalfTest (F i) :=
  ⟨h.borel i,h.bounded.imp fun _ hC => hC i⟩
lemma limit (h : HalfLimit F f) : HalfTest f := by
  obtain ⟨C,hC⟩ := h.bounded
  refine ⟨h.continuous.restrict.measurable,C, fun p hp =>
    le_of_tendsto ((h.converges _ isCompact_singleton (singleton_subset_iff.mpr hp)).tendsto_at
      (mem_singleton p)).norm (.of_forall fun i => hC i p hp)⟩

lemma weak {ν : FiniteMeasure E4} {σ : ℕ → FiniteMeasure E4}
    (h : HalfLimit F f) (hμ : Tendsto σ atTop (𝓝 ν))
    (k : ∀ i, ∀ᵐ p ∂(σ i:Measure E4), p ∈ half)
    (k' : ∀ᵐ p ∂(ν:Measure E4), p ∈ half) :
    Tendsto (fun i => ∫ p, F i p ∂(σ i:Measure E4)) atTop
      (𝓝 (∫ p, f p ∂(ν:Measure E4))) := by
  obtain ⟨C,hC⟩ := h.bounded
  rw [← integral_congr_ae (f:=f ∘ gate) (clamp_ae k')]
  refine (weak_vary hμ (F:=fun i => F i ∘ gate) (f:=f ∘ gate)
    ⟨C,fun i p => hC i _ (gate_mem p)⟩ h.limit.clamp.2
    (fun i => (h.term i).clamp.1) (h.continuous.comp_continuous gate_cont gate_mem) ?_).congr
      fun i => integral_congr_ae (clamp_ae (k i))
  intro K hK
  have h' := h.converges _ (hK.image gate_cont) (image_subset_iff.mpr fun x _ => gate_mem x)
  exact Metric.tendstoUniformlyOn_iff.mpr fun e he =>
    (Metric.tendstoUniformlyOn_iff.mp h' e he).mono fun i hi x hx => hi _ (mem_image_of_mem _ hx)

end HalfLimit

end YM.Six

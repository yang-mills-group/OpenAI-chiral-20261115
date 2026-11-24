import YM.SU5.MacroSix.SmearedBall
/-! # Discount against the *spatial* measure only -/
set_option autoImplicit false
noncomputable section
namespace YM.MacroSix
open Filter Function Set MeasureTheory Metric Complex
open scoped Topology NNReal ENNReal InnerProductSpace BigOperators
open ClockTest Projections Mink OS OS.Semigroup.Balloon

variable (u : Space → ℝ) (g : ℝ → ℝ) (A D : Set E4)

lemma cost_octant (μ : Measure E4) (B : Set Space3) (hB : MeasurableSet B)
    (hD : MeasurableSet D) (v : D ⊆ YM.spatial ⁻¹' B) (ht : D ⊆ Mink.inside)
    (p : SmoothDensity u) (q : TimeDensity g) (t : ℝ≥0) (hp : 0 < t)
    (h : (μ.map YM.spatial).restrict B ≪ volume.restrict B) :
    ∀ᵐ x ∂μ.restrict D, jointCost t (joined u g) x≠0 := by
  let V (x : Space3) := frequencyCost u (WithLp.ofLp x)
  have he : ∀ᵐ x ∂(μ.map YM.spatial).restrict B, V x≠0 :=
    (ae_restrict_of_ae (frequency_pay u p)).filter_mono h.ae_le
  have hV : Continuous V := (frequencyCost_cont p.smooth.continuous p.compact).comp
    (PiLp.continuous_ofLp _ _)
  have hx : ∀ᵐ x ∂μ, spatial x ∈ B → V (spatial x) ≠ 0 :=
    ae_of_ae_map Mink.rest_cont.measurable.aemeasurable ((ae_restrict_iff
      (isClosed_eq hV continuous_const).measurableSet.compl).1 he)
  filter_upwards [ae_restrict_of_ae hx,ae_restrict_mem hD] with x h₁ h₂
  exact cost_product_ne q u t hp x ((Mink.strict_self _).1 (ht h₂)).1 (h₁ (v h₂))

lemma totalMirror (H : Hilbert) (F : Full → H) (G : Full → H) (φ : Full → Full)
    (hφ : MeasurePreserving φ) (hm : MeasurableEmbedding φ) (u : F=G ∘ φ) :
    total H volume F=total H volume G := by
  letI := NormedSpace.restrictScalars ℝ ℂ H.space
  subst F; exact hφ.integral_comp hm G
end YM.MacroSix
#print axioms YM.MacroSix.cost_octant

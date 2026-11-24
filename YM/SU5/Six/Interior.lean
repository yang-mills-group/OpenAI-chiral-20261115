import YM.SU5.Six.JointPM
/-!
# Positivity from prices of interior sets
-/
set_option autoImplicit false
noncomputable section

namespace YM.Six
open Filter Set MeasureTheory Metric
open scoped ComplexOrder

lemma interior_positive {μ : Measure E4} [IsFiniteMeasure μ]
    (hs : ∀ᵐ p ∂μ, p ∈ half)
    (hi : ∀ ⦃U : Set E4⦄, IsOpen U → (Mink.inside ∩ U).Nonempty → 0 < μ U)
    (f : E4 → ℝ) (hc : Continuous f) (hn : ∀ p ∈ half, 0 ≤ f p) (C : ℝ)
    (hb : ∀ p ∈ half, f p ≤ C) (p : E4) (hp : p ∈ Mink.inside) (h : 0 < f p) :
    0 < ∫ p, (↑(f p):ℂ) ∂μ := by
  rw [integral_complex_ofReal]
  suffices ht : 0 < ∫ p, f p ∂μ by exact_mod_cast ht
  have hi' : Integrable f μ :=
    Integrable.of_bound hc.aestronglyMeasurable C (hs.mono fun p hp =>
      le_trans (Real.norm_of_nonneg (hn p hp)).le (hb p hp))
  refine (integral_pos_iff_support_of_nonneg_ae (hs.mono hn) hi').mpr ?_
  exact hi hc.isOpen_support ⟨p,hp,h.ne'⟩

lemma minorant {U : Set E4} (h : IsOpen U) (p) (hp : p ∈ U) :
    ∃ f : E4 → ℂ, Continuous f ∧ f p = 1 ∧
      (∀ w, ‖f w‖ ≤ 1) ∧ (∀ w ∉ U, f w = 0) := by
  obtain ⟨f,h1,h2,h3⟩ := exists_continuous_zero_one_of_isClosed h.isClosed_compl
    isClosed_singleton (disjoint_singleton_right.mpr (show p∉Uᶜ by simpa using hp))
  refine ⟨fun q => ↑(f q), Complex.continuous_ofReal.comp f.continuous,?_,?_,?_⟩
  · change (↑(f p) : ℂ) = _; exact_mod_cast h2 (Set.mem_singleton p)
  · intro w; rw [Complex.norm_real, Real.norm_of_nonneg (h3 w).1]; exact (h3 w).2
  intro w hw; change (↑(f w) : ℂ) = _; exact_mod_cast h1 hw

end YM.Six

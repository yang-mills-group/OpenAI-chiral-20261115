import SU5ExactRunningTarget
import ExactRunning.Final.UV

set_option autoImplicit false

namespace ChiralSU5

open YM.CF.Buffered.Afterglow.Tower.VacuumSelection

/-- The three window measurements share their ultraviolet thresholds and
specialize to the selected cutoff and volume sequence. -/
theorem exactUltravioletRunning (P : Spine) : ExactUltravioletRunning P where
  positiveGaugeIncrement := Spine.Wilsonian.ℓg_pos P
  coefficients ε hε := by
    obtain ⟨J, K, hJ, hK, estimates⟩ := Spine.Wilsonian.uniform_exact_running P ε hε
    refine ⟨J, K, hJ, hK, ?_⟩
    intro j k hj hk i N fits
    obtain ⟨gauge, full, screening⟩ := estimates j k hj hk i N fits
    exact ⟨gauge, screening, full⟩
  windowCoverage := Spine.Wilsonian.diagonal_coverage P

end ChiralSU5

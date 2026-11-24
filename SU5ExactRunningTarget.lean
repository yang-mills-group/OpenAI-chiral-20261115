import SU5RunningTarget

set_option autoImplicit false

namespace ChiralSU5

open Filter
open scoped Topology
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection

/-- Ultraviolet limits of the stationary gauge increment, its excess over the
fitted inverse-coupling increment, and the fitted increment itself. All three
measurements use one window in the same volume row and cutoff. -/
structure ExactUltravioletRunning (P : Spine) : Prop where
  positiveGaugeIncrement : 0 < YM.CF.Vale.billX P.par.R.L
  coefficients :
    ∀ ε : ℝ, 0 < ε → ∃ J K : ℕ, 1 ≤ J ∧ 1 ≤ K ∧
      ∀ j k : ℕ, J ≤ j → K ≤ k → ∀ i N : ℕ, j + k ≤ N →
        let G := gaugeChange P N j k
        let ΔB := inverseCoupling P i N (j + k) - inverseCoupling P i N j
        |coefficient P k G - 55 / 3| < ε ∧
        |coefficient P k (G - ΔB) - 4| < ε ∧
        |coefficient P k ΔB - 43 / 3| < ε
  windowCoverage (j k : ℕ) :
    ∀ᶠ r : ℕ in atTop, (P.run.voyage (P.diagonalᵢ r)).kick ≤ P.diagonalₖ r ∧
      j + k ≤ P.diagonalDepth r

end ChiralSU5

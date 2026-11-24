import GaugeFieldConstructionDesiderata

/-! Ultraviolet measurements on a specified four-dimensional lattice history. -/

set_option autoImplicit false

namespace ChiralSU5

open Filter Finset
open scoped Topology BigOperators
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection

/-- The inverse squared coupling fitted on volume row `i`, at cutoff depth
`N` and resolution `s`. Its endpoint values are taken from that row. -/
noncomputable def inverseCoupling (P : Spine) (i N s : ℕ) : ℝ :=
  (((P.run.voyage i).X N).gram s).beta

/-- Increase of the stationary gauge contribution over `k` RG steps towards
the ultraviolet. The underlying step charges are indexed in the opposite direction. -/
noncomputable def gaugeChange (P : Spine) (N j k : ℕ) : ℝ :=
  -(∑ w ∈ range k, P.par.V.L.charge (N - 1 - (j + w)))

/-- Normalize per-step changes so the leading pure-gauge coefficient is 55/3. -/
noncomputable def coefficient (P : Spine) (k : ℕ) (increment : ℝ) : ℝ :=
  (55 / 3 : ℝ) * increment / ((k : ℝ) * YM.CF.Vale.billX P.par.R.L)

/-- The fitted coefficient, the fermionic screening and coverage of the
selected joint cutoff/volume sequence. Both estimates are uniform in the row
and cutoff once the ultraviolet window fits inside it. -/
structure UltravioletRunning (P : Spine) : Prop where
  positiveGaugeIncrement : 0 < YM.CF.Vale.billX P.par.R.L
  fullCoefficient :
    ∃ J K : ℕ, 1 ≤ J ∧ 1 ≤ K ∧
      ∀ j k : ℕ, J ≤ j → K ≤ k → ∀ i N : ℕ, j + k ≤ N →
        |coefficient P k (inverseCoupling P i N (j+k) - inverseCoupling P i N j)
          - (43/3 : ℝ)| < 43/60
  fermionScreening :
    ∀ ε : ℝ, 0 < ε → ∃ J K : ℕ, 1 ≤ J ∧ 1 ≤ K ∧
      ∀ j k : ℕ, J ≤ j → K ≤ k → ∀ i N : ℕ, j + k ≤ N →
        |coefficient P k (gaugeChange P N j k -
            (inverseCoupling P i N (j+k) - inverseCoupling P i N j)) - 4| < ε
  windowCoverage (j k : ℕ) :
    ∀ᶠ r : ℕ in atTop, (P.run.voyage (P.diagonalᵢ r)).kick ≤ P.diagonalₖ r ∧
      j + k ≤ P.diagonalDepth r

end ChiralSU5

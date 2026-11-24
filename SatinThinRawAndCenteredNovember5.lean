import SatinThinMatrixOnOneElectionNovember5
import YM.SU5.Thin.WhatLimit

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 28000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six

/-- On the identical two smears, the strong-operator raw price is positive
while the earlier ground-field pairing factors exactly. These are two named
readings. This theorem gives no sign to the centered strong-operator price. -/
theorem reviewRawAndCenteredOnOnePair :
    ∃ (P : Spine) (K : P.Register) (c r : ℕ → ℕ) (x : P.Spectrum0 3) (J : P.Ellis 3 x),
      uniform P K thinRequest 1 1 ∧ id ≤ r ∧ P.Repeater K x J r ∧
      P.Experiment K c r x J ∧ P.Strategy K c r x ∧ P.TransSix K x c r ∧
      (∀ cost : Lead.Clan → ℝ, (∀ Z, 0 < cost Z) → ∀ᶠ j : ℕ in atTop,
        ∀ Z, Nonempty (Thinning.Portfolio x (c j) (r j) (cost Z) Z)) ∧
      ∀ᶠ i : ℕ in atTop, ∃ (M : P.Menagerie) (b : ℕ → ℕ) (a : ℝ) (F G : SampleDose)
        (D : ∀ Z : Lead.Clan, P.VoucherOp x Z (r i) b),
        P.GetsThin K x c r i a F G b D ∧
        P.Dawn K x (c i) (r i) reviewEarlierBox reviewLaterBox fullWay F G M ∧
        P.FixedSatinReadings K x (c i) (r i) a F G ∧
        Tendsto (fun j : ℕ => P.slopeReading x (c j) (r j) 0 F G) atTop (𝓝 (0 : CrossRead)) ∧
        ∀ Z W : Lead.Clan,
          purePrice Z * purePrice W / 2 < ‖jointPrice P x r i F G b Z W D‖ ∧
          let z := P.finalPairing x Z W F G
          z.1 - z.2.1 * z.2.2 = 0 := by
  obtain ⟨P, K, c, r, x, J, h, hr, W, E, S, matrix, carriers, pairs⟩ :=
    reviewThinAssayAndSixMatrix
  refine ⟨P, K, c, r, x, J, h, hr, W, E, S, matrix, carriers, ?_⟩
  filter_upwards [pairs] with i claim
  obtain ⟨M, b, a, F, G, D, thin, dawn, raw, slope⟩ := claim
  refine ⟨M, b, a, F, G, D, thin, dawn, raw, slope, ?_⟩
  intro Z V
  refine ⟨(thin.channel Z V).interaction, ?_⟩
  exact sub_eq_zero.mpr (actualDisconnected P x Z V F G thin.oldData.1 thin.oldData.2.1)

#print axioms actualDisconnected
#print axioms reviewRawAndCenteredOnOnePair
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

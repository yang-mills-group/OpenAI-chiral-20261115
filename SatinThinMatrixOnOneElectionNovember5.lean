import SatinThinAssayOnOnePairNovember5
import YM.SU5.MacroSix.Main

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

/-- The matrix calculation and the thin experiment use the same launch, party,
ultraviolet calibration, spectral summit and reflected lower-deck data. -/
theorem reviewTransSixOfExperiment {P : Spine} {K : P.Register} {c r : ℕ → ℕ}
    {x : P.Spectrum0 3} {J : P.Ellis 3 x} (E : P.Experiment K c r x J) :
    P.TransSix K x c r := by
  have chosen : P.Chosen x K c r J := ⟨E.launch, E.ground, E.ready, E.top, E.realPos⟩
  exact transSix chosen

/-- The full six-channel spectral statement holds on the very same elected
trajectory as the thin pair. Its spectral windows and allowed reflected tests
retain the qualifications of TransSix. -/
theorem reviewThinAssayAndSixMatrix :
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
        Tendsto (fun j : ℕ => P.slopeReading x (c j) (r j) 0 F G) atTop (𝓝 (0 : CrossRead)) := by
  obtain ⟨P, K, c, r, x, J, h, hr, W, E, S, carriers, pairs⟩ := reviewThinAssayOnOnePair
  exact ⟨P, K, c, r, x, J, h, hr, W, E, S, reviewTransSixOfExperiment E, carriers, pairs⟩

#print axioms reviewTransSixOfExperiment
#print axioms reviewThinAssayAndSixMatrix
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

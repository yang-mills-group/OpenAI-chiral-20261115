import SatinGlasshouseReadingNovember6
import SatinProbeCompatibilityNovember6
import YM.SU5.Reconstruction.GiftWrap.Encounter

/-! The two CP18 smears in the CP27 display, retaining their chosen
character and ordered product. CP27's registration and boost estimates are
listed as hypotheses for the subsequent field-interpretation theorem. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
namespace Spine
open Aria Casting Six MacroGrid SatinNucleus SatinJets DoseTravel Set

def glasshouseCentered (P : Spine) (x : P.Spectrum0 3) (t : ℕ) (f g : P.Test) : ℂ :=
  let read := fun u : P.Test => Selected.response P.run P.large P.law t P.history
    P.projection.clipped 3 false (P.room 3) (P.glasshouseCharacter 3 x) (P.glasshouseMark u)
  read (f * g) - read f * read g

variable (P : Spine) (x : P.Spectrum0 3) (A : ℕ → P.Apron) (c r n : ℕ → ℕ)
variable (w : Lead.Clan → Prism) (F U : SampleDose)

def glasshousePrism (i t : ℕ) : CrossRead :=
  Matrix.of fun a b : Lead.Clan => P.glasshouseCentered x t
    (P.prepared t (((P.soldTrumpet A c r n w) a i).kiss P 3) F)
    (P.prepared t ((P.soldTrumpet A c r n w) b i) U)

/-- Equality of all 36 centered readings on the fixed smears, at every
consultation, under the literal identification of the selected display. -/
theorem glasshousePrism_eq_azure (i t : ℕ) :
    P.glasshousePrism x A c r n w F U i t = P.azurePrism x A c r n w F U i t := by
  funext a b
  exact (P.azureBeaconOnPrepared x t (((P.soldTrumpet A c r n w) a i).kiss P 3)
    ((P.soldTrumpet A c r n w) b i) F U).symm

/-- This specializes CP27's general criterion to the same character used by
the disclosed thin experiment. The two required physical inputs are explicit. -/
theorem glasshouseEnclosure_onSelectedCharacter (j : Axis)
    (backing : FirstWindows.LightBudget.BoostBacking P.run P.large P.law P.projection
      P.room 3 (P.glasshouseCharacter 3 x))
    (registered : FirstWindows.LightBudget.Crease.Registered P.run P.large P.law P.projection
      P.room 3 (P.glasshouseCharacter 3 x) j) :
    FirstWindows.LightBudget.Crease.Enclosure P.run P.large P.law P.projection
      P.room 3 (P.glasshouseCharacter 3 x) j :=
  (FirstWindows.LightBudget.Crease.Boots.decision P.run P.large P.law P.projection
    P.room 3 (P.glasshouseCharacter 3 x) backing j).complete registered

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

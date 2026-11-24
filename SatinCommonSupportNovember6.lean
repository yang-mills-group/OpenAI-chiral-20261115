import SatinProbeCompatibilityNovember6
import YM.SU5.FiniteGaugeData.Dally.Portent

/-! Tighten finite support certificates for the actual two native CP18 insertions
without changing either observable, the fixed separated boxes or the selected state. -/

set_option autoImplicit false
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight

namespace Spine

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set

theorem azurePinFoot_mono (P : Spine) (t : ℕ) {S T : Finset Cover} (incl : S ⊆ T) :
    P.pinFoot t S ⊆ P.pinFoot t T := by
  intro z hz
  obtain ⟨i, hi, covered⟩ := hz
  exact ⟨i, incl hi, covered⟩

variable (P : Spine) (x : P.Spectrum0 3)
variable (A : ℕ → P.Apron) (c r n : ℕ → ℕ) (w : Lead.Clan → Prism)
variable (V : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j))
variable (g h : ℕ) (T' : P.HandleWith x c r A n) (F U : SampleDose)
variable {C L : Doorway} {s k : ℕ} {K' : P.Register} {μ : ℝ}

theorem fullPrism_azure_common_boxes
    (D : P.FullPrismLab x A c r n w V g h T' μ F U C L s k K') :
    ∀ᶠ i in atTop, ∀ t : ℕ, c (n i) ≤ t → ∀ a b : Lead.Clan,
      ∀ S' Q' : Finset Cover,
      Charm.Locator P.calibration (P.azurePrepared t (((P.soldTrumpet A c r n w) a i).kiss P 3) F) S' →
      Charm.Locator P.calibration (P.azurePrepared t ((P.soldTrumpet A c r n w) b i) U) Q' →
      ∃ S Q : Finset Cover,
        Charm.Locator P.calibration (P.azurePrepared t (((P.soldTrumpet A c r n w) a i).kiss P 3) F) (S ∩ S') ∧
        Charm.Locator P.calibration (P.azurePrepared t ((P.soldTrumpet A c r n w) b i) U) (Q ∩ Q') ∧
        P.pinFoot t (S ∩ S') ⊆ C.invites ∧ P.pinFoot t (Q ∩ Q') ⊆ L.invites := by
  filter_upwards [P.fullPrism_azure_boxes x A c r n w V g h T' F U D] with i box
  intro t ht a b S' Q' left right
  obtain ⟨S, Q, locS, locQ, footS, footQ⟩ := box t ht a b
  exact ⟨S, Q,
    Portent.Lands P.calibration S S' _ locS left,
    Portent.Lands P.calibration Q Q' _ locQ right,
    (P.azurePinFoot_mono t (fun _ hi => (Finset.mem_inter.mp hi).1)).trans footS,
    (P.azurePinFoot_mono t (fun _ hi => (Finset.mem_inter.mp hi).1)).trans footQ⟩

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

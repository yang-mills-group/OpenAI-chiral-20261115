import YM.SU5.Same.Sunlit
import SatinStress.Actual.BareFlavor

/-! The zero-heat vacuum vectors and two-point distributions use the same preparation
and elected character as the fixed probes. This entry also records exact flavor
invariance of that preparation's bare density at every cutoff. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 300000
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
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set

open _root_.YM.SatinEdge.RealSheet Boundary Probe

/-- Flavor invariance of the actual top-layer density on this preparation. -/
def BareFlavorAtTop (P : Spine) : Prop :=
  ∀ (i k : ℕ) (z : Orbit (side P.run i (P.run.uv k))) (g : SatinStressData.Flavor),
        acts (quant (SatinStressData.gen (side P.run i (P.run.uv k)) (SatinStressData.turn g)))
          (denZ (((P.run.voyage i).X (P.run.uv k)).gram (P.run.uv k)) P.par.U ((P.run.voyage i).CapeT (P.run.uv k)) z) =
          denZ (((P.run.voyage i).X (P.run.uv k)).gram (P.run.uv k)) P.par.U ((P.run.voyage i).CapeT (P.run.uv k)) z

/-- The bare symmetry holds for the same preparation that supplies the unpadded readings. -/
theorem sunlit_real_prism_with_bare_flavor :
    ∃ (P : Spine) (K : P.Register) (c r : ℕ → ℕ) (x : P.Spectrum0 3)
      (R : P.Ellis 3 x) (i₀ : ℕ) (F U : SampleDose),
      P.BareFlavorAtTop ∧
      (∀ i k : ℕ, (((P.run.voyage i).X (P.run.uv k)).gram 0).beta = P.par.x) ∧
      Experiment P K c r x R ∧ P.Transmission x c r ∧ F.Normalized ∧ U.Normalized ∧
      tsupport F.val ⊆ reviewEarlierBox.invites ∧ tsupport U.val ⊆ reviewLaterBox.invites ∧
      P.ReturnsSix x (c i₀) (r i₀) 0 F U ∧ P.FixedSatinReadings K x (c i₀) (r i₀) 0 F U ∧
      ∃ (A : ℕ → P.Apron) (n : ℕ → ℕ) (w : Lead.Clan → Prism)
        (V : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j))
        (g h : ℕ) (X : P.HandleWith x c r A n),
        P.FullPrismLab x A c r n w V g h X 1 F U reviewEarlierBox reviewLaterBox
          (c i₀) (r i₀) K ∧
        (∃ d : marks (timeMesh P.par), P.LabRegistry x A c r n w F U X V d ∧
          (∀ i, PureGauge P.calibration (A i).F) ∧
          P.SplitShadow x A c r n w F U X V ∧
          ∀ᶠ i in atTop, ∀ t : ℕ, c (n i) ≤ t → ∀ a : Lead.Clan, P.PulseNullBudget x A c r n w F U d i t a) ∧
        PoweredHeat P x V ∧
        (∃ (Y : Lead.Clan → Test4 →L[ℂ] P.ManyF 3 (P.advocate 3 x 3))
          (Z : Lead.Clan → Lead.Clan → Boundary.Distn E4),
          P.AtZeroHeat x A c r n w V X F U Y Z) ∧
        (∀ a:Lead.Clan,
            TemperedAtEdge (P.ColorHil 3 (P.advocate 3 x 3)) (P.profilesH x w a V) ∧
            TemperedAtEdge (P.ManyF 3 (P.advocate 3 x 3)) (P.profilesZ x V w a)) ∧
        (∃ d : ℝ, 0 < d ∧ LoudMargin (P.readPrism x V w 1 F U) d ∧
          ∀ᶠ i in atTop, ∀ t : ℕ, c (n i) ≤ t → LoudMargin (P.azurePrism x A c r n w F U i t) d) ∧
        ((∀ᶠ i in atTop, Tendsto (fun t => P.azurePrism x A c r n w F U i t) atTop
          (𝓝 (P.thinJournal x A c r n w X F U i))) ∧
          Tendsto (P.thinJournal x A c r n w X F U) atTop (𝓝 (P.readPrism x V w 1 F U))) ∧
        ∀ᶠ i in atTop, ∀ t : ℕ, c (n i) ≤ t → ∀ a : Lead.Clan,
          ∀ u : Charm.W P.calibration, Verne.GNative P.calibration u →
            (P.prepared t (((P.soldTrumpet A c r n w) a i).kiss P 3) F).val ≠ u.val ∧
            (P.prepared t ((P.soldTrumpet A c r n w) a i) U).val ≠ u.val := by
  obtain ⟨P, K, c, r, x, R, i, F, U, data⟩ := sunlit_real_prism
  exact ⟨P, K, c, r, x, R, i, F, U, inherited P, data⟩

#print axioms sunlit_real_prism_with_bare_flavor
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

import SU5SatinFixedProbesAndBareFlavorNovember6
import YM.SU5.Registration.RapidBoundary
/-!
# One fixed realization, the interface in `the construction notes`

Expose the data of `Spine.sunlit_real_prism`, *including* Y Z, for reusable
results. No extraction of a different character/field map when consuming this
interface. We can require extra estimates delivered in picking the tuple for
the existence goal; no assumption made here as to whether they are achievable
or whether all of these tuples can subsequently satisfy them.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 700000
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

/-- Field registration starts at exactly this tuple's preparation and elected character. -/
structure M4Tuple (P : Spine) (K : P.Register) (c r : ℕ→ℕ) (x : P.Spectrum0 3) (R : P.Ellis 3 x)
    (i₀ : ℕ) (F U : SampleDose) (A : ℕ → P.Apron) (n : ℕ→ℕ) (w : Lead.Clan → Prism)
    (V : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j)) (g h : ℕ)
    (X : P.HandleWith x c r A n)
    (Y : Lead.Clan → Test4 →L[ℂ] P.ManyF 3 (P.advocate 3 x 3)) (Z : Lead.Clan → Lead.Clan → Boundary.Distn E4) : Prop where
  calibration : ∀ i k : ℕ, (((P.run.voyage i).X (P.run.uv k)).gram 0).beta = P.par.x
  experiment : Experiment P K c r x R
  transmit : P.Transmission x c r
  normF : F.Normalized
  normU : U.Normalized
  inF : tsupport F.val ⊆ reviewEarlierBox.invites
  inU : tsupport U.val ⊆ reviewLaterBox.invites
  six : P.ReturnsSix x (c i₀) (r i₀) 0 F U
  fixed : P.FixedSatinReadings K x (c i₀) (r i₀) 0 F U
  lab : P.FullPrismLab x A c r n w V g h X 1 F U reviewEarlierBox reviewLaterBox (c i₀) (r i₀) K
  work : ∃ d : marks (timeMesh P.par), P.LabRegistry x A c r n w F U X V d ∧
          (∀ i, PureGauge P.calibration (A i).F) ∧
          P.SplitShadow x A c r n w F U X V ∧
          ∀ᶠ i in atTop, ∀ t : ℕ, c (n i) ≤ t → ∀ a : Lead.Clan, P.PulseNullBudget x A c r n w F U d i t a
  powered : PoweredHeat P x V
  zeroHeat : P.AtZeroHeat x A c r n w V X F U Y Z
  tempered : (∀ a:Lead.Clan,
            TemperedAtEdge (P.ColorHil 3 (P.advocate 3 x 3)) (P.profilesH x w a V) ∧
            TemperedAtEdge (P.ManyF 3 (P.advocate 3 x 3)) (P.profilesZ x V w a))
  margin : (∃ d : ℝ, 0 < d ∧ LoudMargin (P.readPrism x V w 1 F U) d ∧
          ∀ᶠ i in atTop, ∀ t : ℕ, c (n i) ≤ t → LoudMargin (P.azurePrism x A c r n w F U i t) d)
  arrives : ((∀ᶠ i in atTop, Tendsto (fun t => P.azurePrism x A c r n w F U i t) atTop
          (𝓝 (P.thinJournal x A c r n w X F U i))) ∧
          Tendsto (P.thinJournal x A c r n w X F U) atTop (𝓝 (P.readPrism x V w 1 F U)))
  excludes : ∀ᶠ i in atTop, ∀ t : ℕ, c (n i) ≤ t → ∀ a : Lead.Clan,
          ∀ u : Charm.W P.calibration, Verne.GNative P.calibration u →
            (P.prepared t (((P.soldTrumpet A c r n w) a i).kiss P 3) F).val ≠ u.val ∧
            (P.prepared t ((P.soldTrumpet A c r n w) a i) U).val ≠ u.val

lemma tuple_from_sunlit : ∃ (P : Spine) (K : P.Register) (c r : ℕ→ℕ) (x : P.Spectrum0 3) (R : P.Ellis 3 x)
    (i₀ : ℕ) (F U : SampleDose) (A : ℕ → P.Apron) (n : ℕ→ℕ) (w : Lead.Clan → Prism)
    (V : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j)) (g h : ℕ)
    (X : P.HandleWith x c r A n)
    (Y : Lead.Clan → Test4 →L[ℂ] P.ManyF 3 (P.advocate 3 x 3)) (Z : Lead.Clan → Lead.Clan → Boundary.Distn E4),
    M4Tuple P K c r x R i₀ F U A n w V g h X Y Z := by
  obtain ⟨P,K,c,r,x,R,j,F,U,B,e,t,q₀,q₁,u,v,z,f,A,n,w,V,g,h,X,M,T,p,⟨Y,Z,s⟩,y,k,d,l⟩:= sunlit_real_prism
  exact ⟨P,K,c,r,x,R,j,F,U,A,n,w,V,g,h,X,Y,Z,B,e,t,q₀,q₁,u,v,z,f,M,T,p,s,y,k,d,l⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

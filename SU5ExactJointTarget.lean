import SU5RelativisticTarget
import SU5ExactRunningTarget
import GaugeFieldConstructionDesiderata
import GaugeFieldConstruction.SeasonPlural
import GaugeFieldConstruction.TextureOnTape

/-! The same reconstructed vacuum supports the stress tensor, the handedness
and mixed tests, and the selected lattice history used for the running test. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 7200
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
open RosterJ BoonsθJ SignetS Patrons ChSigFe
open CF.XGarden.MastTin.ArtCart
open SpaΘ
open Fock.Flux
open Papal
open Yoke SelectionAnalysis
open Oath.BellPrice
open GaugeFieldConstruction.Phys
open Fock
open GaugeFieldConstruction
open Fathom Ember
open Calibration.Floor Calibration

open Ember.Volumetric Ember.Volumetric.FirstPackMars Mavera
open Shower
open Calibration Calibration.Floor
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick YM.GaugeFieldConstruction.Cauchy
open SelectionAnalysis
open CF.Levier CF.Spire
open Fathom Ember Hulse Points Fathom.Salam Fathom.Palace

namespace ContinuumConstruction
open Discipline
open _root_.YM.SatinWFixed Andesite Carton InkPort
open _root_.YM.Boundary (Test4)
open _root_.YM.SatinRegistration
open NSF.Boundary
namespace GaugeLimitJoint
open _root_.YM.LocalFieldBounds
open Motif (late_at smallCast programme_plus Programme Production)
open _root_.YM.WakeFields
open QuadClock ShapeLab SignSlot
open Spine.Fame.Regulator Internal Dovetail Freeport Polaris
open SoulField SatinWard.Installment Ione.Clock Moto
open LitCurrent LitCurrent.AuroraX
open _root_.GarnetAct.Cut
open Set MeasureTheory
open CF.LitCurrent.AuroraX
open Motif
open _root_.YM.GaugeFieldConstruction.Stage _root_.YM.GaugeFieldConstruction.Stage.Cell
open Reconstruction AcrossLands SecondSeason SecondOrient

/-- For arbitrarily large reference inverse squared coupling there is a
three-generation chiral SU(5) history and a reconstructed theory of local
observables with positive energy, a cyclic vacuum and a unitary Poincaré
action. The three-current measurements in the 10 and conjugate 5 channels
recover their respective left-handed values on this state.

A matter current from a single generation and a gauge-field observable have
a nonzero connected vacuum correlation on compact, spacelike-separated
supports. The witnesses below identify the first-generation 10 current and
the gauge clover with their corresponding lattice insertions. The ultraviolet
gauge, screening and fitted coefficients on this history converge to 55/3,
4 and 43/3 with common thresholds for every positive tolerance. -/
def _root_.ChiralSU5.InteractingThreeGenerationTheoryWithExactRunning : Prop :=
  ∀ b : ℝ, ∃ (nLeaf : ℕ) (y : Project b),
    y.P.par.x > b ∧
    ∃ (production : YardμN y.P CostUpVU PolRun PriceArtVU nLeaf)
      (growth : InterR) (roles : ConsoleθN production ΓmotVU 0 growth ΓstageVU)
      (axes : Axis → GaugeFieldConstruction.Empire.Across) (comparison : Sheds roles.Crew_N axes)
      (approvals : Supplies comparison) (stress : Ticket roles.Gamma_N approvals)
      (a : GivenTime y) (costAnalysis : y.P.Ellis 3 a.guest.atx) (c collars : ℕ → ℕ)
      (layers : NSF.Boundary.Waves (roles.RadianceVU stress))
      (response : NSF.Boundary.Surface (roles.RadianceVU stress))
      (continued : NSF.Boundary.Surface.Aurora response NSF.LD.drapeL)
      (model : roles.GlowVU stress a.guest.atx (le_refl _) layers response)
      (screens : y.P.Poll 3)
      (C : Assembled (scale := y.U) (costAnalysis := costAnalysis) (c := c)
        (collars := collars) (continued := continued) (model := model) (screens := screens)),
      OneTheory C ∧ RelativisticClauses C ∧
      SeparatedHandedReadings (scale := y.U) (stress := stress)
        (vacuum := a.guest.atx) (screens := screens) ∧
      ChiralSU5.ExactUltravioletRunning y.P ∧
      ∃ (τ : ℕ) (ε β : ℕ → ℝ) (U : TemperListSt y.P β y.U τ ε),
        CrossCapitalSt (vacuum := a.guest.atx) (screens := screens) U ∧
        (∀ (m : Side) (k : ℕ) (h : y.P.FrontalAccessSt m k τ), FullAmplitudeSt y.P m k β h) ∧
        DeterminesSeasonSt (roles := roles) (stress := stress) (vacuum := a.guest.atx)
          (response := response) (screens := screens) U ∧
        ∃ (r : GlyphSt),
        WithTypefaceSt (stress := stress) (vacuum := a.guest.atx) r ∧
        ∀ᶠ k in atTop, ∃ (t : roles.LeaseVU k), ∃ X F W u PCI Ψ,
          MatineeSt (β := β) (F := F) (W := W) (a := a) (u := u) (model := model)
            (continued := continued) (t := t) (r := r) (screens := screens)
            (c := c) (collars := collars) k X PCI Ψ 1 ∧
          let matterSmearing := Easel.film a.guest.first
          let gaugeSmearing := Easel.film a.guest.last
          let matterCurrent :=
            ((↑(a.guest.sig) : ℂ) • JXSt (model := model) (a := a) k X a.guest.i) matterSmearing
          let gaugeObservable := KXSt (model := model) (a := a) k X gaugeSmearing
          let Ω := model.system.operators.omega
          IsCompact (tsupport matterSmearing) ∧ IsCompact (tsupport gaugeSmearing) ∧
          (∀ x ∈ tsupport matterSmearing, ∀ z ∈ tsupport gaugeSmearing, x - z ∈ Mink.spacelike) ∧
          inner ℂ Ω (gaugeObservable Ω) = 0 ∧
          (inner ℂ Ω (matterCurrent (gaugeObservable Ω)) -
            inner ℂ Ω (matterCurrent Ω) * inner ℂ Ω (gaugeObservable Ω)).re ≠ 0

end GaugeLimitJoint
end ContinuumConstruction
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end

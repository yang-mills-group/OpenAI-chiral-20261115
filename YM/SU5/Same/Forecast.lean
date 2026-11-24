import SU5SatinVerifiedNovember6
import YM.SU5.Same.TicketsPrism

import YM.SU5.Same.BareReading
import YM.SU5.Same.PulseAssessment
/-!
 # M2 Main application, still partial. See the construction notes
 -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 4000
set_option maxHeartbeats 500000
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
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget

variable (P : Spine) (x : P.Spectrum0 3) (A : ℕ → P.Apron) (c r n : ℕ → ℕ)
    (w : Lead.Clan → Prism) (F U : SampleDose)
local notation "j" => (3:Axis)
local notation "C'" => reviewEarlierBox
local notation "B'" => reviewLaterBox
local notation "W₁" a:max i:max => (((P.soldTrumpet A c r n w) a i).kiss P 3)
local notation "W₂" b:max i:max => ((P.soldTrumpet A c r n w) b i)
local notation "f₁" t:max a:max i:max => P.prepared t (W₁ a i) F
local notation "f₂" t:max a:max i:max => P.prepared t (W₂ a i) U
local notation "ξ" z:max => P.advocate 3 x z
local notation "K" => P.calibration
local notation "S" => P.ColorHil j (ξ j)
local notation "S'" => P.ManyF j (ξ j)
local notation "R" => P.glassSpace 3 x j
local notation "X₂" => P.glassFort 3 x j
local notation "Ω" => P.glassVac 3 x j
local notation "Ω₂" => P.glassHeaven 3 x j
local notation "ι₂" => P.fortIn 3 x j
local notation "Λ₀" => P.glasshouseCharacter 3 x
local notation "λ₁" => opCarries P.run P.large P.law P.projection 3 (P.room 3) (P.glassAxis 3 x 3)
local notation "Hc" => Crease.Charter P.run P.large P.law P.projection P.room j Λ₀ j
local notation "Wc" => Crease.floor P.run P.large P.law P.projection P.room j Λ₀ j
local notation "K!" => P.toFort 3 x j
local notation "J!" => P.toGlass 3 x j
variable (T' : P.HandleWith x c r A n)
    (V : ∀ z : Axis, List Axis → ℝ → P.ColorHil z (P.advocate 3 x z))
    (d : marks (timeMesh P.par))
local notation "m!" i:max => c (n i)
local notation "X!" z:max => DoseTravel.beam (S') F (P.earlierProfile x V w 1 z)
local notation "Y!" z:max => DoseTravel.beam (S') U (P.laterProfile x V w 1 z)
local notation "w!" => BoostBacking P.run P.large P.law P.projection P.room j Λ₀
local notation "r!" => Crease.Registered P.run P.large P.law P.projection P.room j Λ₀ j

theorem exists_shadow_ticketed_lab : ∃ (P : Spine) (K' : P.Register) (c r : ℕ → ℕ)
    (x : P.Spectrum0 3) (J : P.Ellis 3 x) (i₀ : ℕ) (F U : SampleDose),
    (∀ i k : ℕ, (((P.run.voyage i).X (P.run.uv k)).gram 0).beta = P.par.x) ∧
    Experiment P K' c r x J ∧ P.Transmission x c r ∧ F.Normalized ∧ U.Normalized ∧
    tsupport F.val ⊆ reviewEarlierBox.invites ∧ tsupport U.val ⊆ reviewLaterBox.invites ∧
    P.ReturnsSix x (c i₀) (r i₀) 0 F U ∧ P.FixedSatinReadings K' x (c i₀) (r i₀) 0 F U ∧
    ∃ (A : ℕ → P.Apron) (n : ℕ → ℕ) (w : Lead.Clan → Prism)
      (V : ∀ z : Axis, List Axis → ℝ → P.ColorHil z (P.advocate 3 x z))
      (g h : ℕ) (T' : P.HandleWith x c r A n),
      P.FullPrismLab x A c r n w V g h T' 1 F U reviewEarlierBox reviewLaterBox
        (c i₀) (r i₀) K' ∧
      ∃ d : marks (timeMesh P.par), P.LabRegistry x A c r n w F U T' V d ∧
        (∀ i, PureGauge P.calibration (A i).F) ∧
        P.SplitShadow x A c r n w F U T' V ∧
        ∀ᶠ i in atTop, ∀ t : ℕ, c (n i) ≤ t → ∀ a : Lead.Clan, P.PulseNullBudget x A c r n w F U d i t a := by
  obtain ⟨P,K',_,b,c,r,x,J,_,e,t,_,i,F,U,p,q,v,v',six,fixedRead,g,k,a,y,d,σ,V,n,M,w,u,_⟩ :=
    disclosed_satin_witness
  obtain ⟨d',l⟩ := Schedule.very_late (daylight (timeMesh P.par)) (a:=2)
  let A := P.cinema x g k a y σ d
  have he(i) : PureGauge P.calibration (A i).F := P.cinema_pure ..
  exact ⟨P,K',c,r,x,J,i,F,U,b,e,t,p,q,v,v',six,fixedRead,A,n,w,V,g,k,M,u,
    d',P.registerMatched x A c r n w F U M V d' g k _ _ K' u l.le,he,
    P.earnsSplitShadow x A c r n w F U M V g k J u he,
    P.pulse_components x A c r n w F U M d' V g k u l.le⟩

#print axioms exists_shadow_ticketed_lab
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

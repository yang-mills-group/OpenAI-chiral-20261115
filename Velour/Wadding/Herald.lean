import Velour.Wadding.Glints
/-! # Reunion on the M4 tuple -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 1250000
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

open YM.Velour

variable {P:Spine}{K:P.Register}{c r:ℕ→ℕ}{x:P.Spectrum0 3}
local notation "ξ"=> P.advocate 3 x 3
local notation "ω"=> P.colorZero 3 ξ
local notation "σ"=> P.physicalEnergy 3 ξ
local notation "π'"=> P.wealth 3 ξ
local notation "ℋ"=> P.ColorHil 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "ℰ"=> P.seasons 3 ξ
local notation "C"=> Lead.Clan
variable {R:P.Ellis 3 x}{i₀:ℕ}{F U:SampleDose}{A:ℕ→P.Apron}{n:ℕ→ℕ}{w:C→Prism}
    {V: ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j)}
    {g h : ℕ} {X : P.HandleWith x c r A n}
variable {realY : C → Test4 →L[ℂ] P.ManyF 3 (P.advocate 3 x 3)}{Z:C→C→Boundary.Distn E4}
local notation "𝓕₄"=> M4Furnish P K c r x R i₀ F U A n w V g h X realY Z
local notation "𝓑"=> P.Bobbin 3 ξ
local notation "D"=> (ℰ).muslin
local notation "Ω"=> P.firstTulle 3 ξ
local notation "θ"=> P.detects 3 ξ
local notation "Q"=> P.bobQuote 3 ξ
local notation "γ"=> P.ThinVelour x A c r n w
local notation "Λ"=> P.profilesZ x V w

namespace M4Furnish
variable (u:M4Furnish P K c r x R i₀ F U A n w V g h X realY Z)(e:P.ThinVelour x A c r n w)
local notation "ς"=> P.heaven 3 ξ
local notation "Β"=> u.violet e
local notation "M"=> (ℰ).unit.translation

structure AtSpindle (u:𝓕₄)(e:γ) :Prop where
 charter : (ℰ).Fray Q θ
 bright: ∀v:G,∀ᵐ p ∂ ((ℰ).ℚmeasure.diagonal v), 0 ≤ p (3:Axis)
 serene: ∀v:G,v∈Submodule.span ℂ {ς} ↔ ∀b,M b v=v
 one:‖ς‖=1
 reading(a:C)(f:Test4):
   (θ (u.violet e a) f Ω).val=realY a f
 realSeal(a b:C):
   inner ℂ (Ω).val ((u.garnet e a*u.peridot e b) Ω).val=Z a b (tieAt (sachet_LocalFieldBounds F) (sachet_LocalFieldBounds U))
 euSeal(a b:C):
   inner ℂ ς ((u.redGold e a * u.greenGold e b) ς)=P.readPrism x V w 1 F U a b

theorem reunion : AtSpindle u e:=
 ⟨P.satin_storage ..,P.char_positive 3 ξ, P.first_emperor 3 ξ u.emperor,
   P.stone_norm ..,u.lofty_val e,u.jewel_boundary e,u.jewels_paid e⟩


local notation "J"=> P.reportPrism A c r n w F U
local notation "I₁"=> P.gaugeShadowPrism A c r n w F U
local notation "𝒴"=>P.readPrism x V w 1 F U
local notation "O"=>P.gaugeTrumpet A c r n w

/-- Negative comparison information, in tandem with reunion: the different
fixed-smear comparison forecasts survive **on presentation data** despite
identity of the registered channels. Entire price and field maps coincide on
those substitutions. This tests a notion of intrinsic which would require
such a forecast to descend even among these presentations. Does *not*
test for the absence of any form of interaction.
 -/
def Contrasts (u:𝓕₄)(e:γ):Prop:=
 (∀a:C, ∃η:𝓑,
    η.spool=O a ∧ (∀i, PureGauge P.calibration (O a i).F)
    ∧ (∀d,0<d → Q η d=Q (u.violet e a) d)
    ∧ θ η= θ (u.violet e a) ∧ θ η.windBack=θ (u.violet e a).windBack)
 ∧ (∀t:ℕ→ℕ,(∀ᶠ i in atTop,c (n i)≤t i) →
      Tendsto (fun i=>I₁ i (t i) (P.thinSplit x (t i))) atTop (𝓝 𝒴) ∧
      Tendsto (fun i=>J i (t i) (P.thinSplit x (t i))) atTop (𝓝 0))
 ∧ ∀a:C,𝒴 a a ≠0

variable (y:M4Velvet P x A c r n)

theorem foil : Contrasts u (y.thin w X u.experiment):=by
 obtain ⟨d,h,p,k,t⟩:=u.split
 refine ⟨?_,fun m b=>⟨?_,?_⟩,?_⟩


 · let e:=y.thin w X u.experiment
   intro a
   obtain ⟨b,m,cb⟩:=y.both K w X R u.experiment a
   let η:𝓑:={
               spool:=O a
               thin:=fun j=>
                (u.lab.armada.slender a j).congr (fun i=>(k.budgetWidth a i j).symm)
               ribbon:=m }
   have eq (d:ℝ≥0)(g:0<d):Q η d=Q (u.violet e a) d:=
     congrArg (P.tableau 3 ξ 0) (cb d g).symm
   have a':=P.satin_storage 3 ξ
   refine ⟨η,rfl,k.pureField a,eq,
      (a'.1 η).common (a'.1 (u.violet e a)) (eventually_mem_nhdsWithin.mono fun _ z=>eq _ z),
      (a'.1 η.windBack).common (a'.1 (u.violet e a).windBack) ?_⟩
   exact eventually_mem_nhdsWithin.mono fun d z=>
     ((η.backward z).symm.trans (congrArg _ (eq d z))).trans ((u.violet e a).backward z)
 · exact (k.owns m b).2
 · exact (k.mixedForecast m b).1
 · exact u.lab.all_six.2

#print axioms foil
#print axioms reunion
end M4Furnish
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection


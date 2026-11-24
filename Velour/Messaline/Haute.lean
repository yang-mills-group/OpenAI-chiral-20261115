import Velour.Lustre.Gowns
import Velour.Messaline.Featured
import Velour.Ispahan.Cash
import Velour.Sequins.Dazzle
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 400000
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

open OS.Semigroup.Livery
namespace M4Furnish
variable (u:M4Furnish P K c r x R i₀ F U A n w V g h X realY Z)
local notation "Y"=> P.glimmers x 3
local notation "N"=> (ℰ).nursery (P.glimmers x 3) (P.firstTulle 3 ξ)
local notation "M"=>Module.End ℂ (D)


/-- Livery of this tuple. -/
abbrev haute:=P.wears x 3 u.emperor

/-- Exact remaining wave-speed estimate in this criterion. **No**
 angular Ward identity or tilted rep in this one. -/
def Thirst (P:Spine)(x:P.Spectrum0 3):Prop:=
 ∀b:SpaceAxis, Nonempty ((P.seasons 3 (P.advocate 3 x 3)).Tiles (OS.Semigroup.royal b)) ∧
   Nonempty ((P.seasons b.castSucc (P.advocate 3 x b.castSucc)).Tiles (OS.Semigroup.royal b).symm)

lemma tucked (p:Thirst P x):u.haute.Blithe:=
 ⟨P.meander x 3,fun b=>⟨(p b).1,P.ManyF b.castSucc (P.advocate 3 x b.castSucc),
   P.seasons b.castSucc (P.advocate 3 x b.castSucc),
   P.wears x b.castSucc (u.experiment.ground.1 _),
   P.excels x 3 u.emperor b.castSucc (u.experiment.ground.1 _) R, (p b).2⟩⟩

/-- Under wave-speed estimate, on restriction to nursery (even word closure in
all graphs): local commutation and true cone. Use also for Featured via
`story_pocket`, which just enriches with actual positive-time labels (also
`story_nursery`). -/
structure HauteTruth (u:𝓕₄): Prop where
 fresh: u.haute.Blithe
 honest:∀(E W:Set E4), (∀x∈E,∀y∈W,y-x∈Mink.spacelike)→
   ∀{p q:M},p∈pocket Y E→q∈pocket Y W→u.haute.Partner p q
 healthy:{v:G}→v∈N → (ℰ).ℚmeasure.region (Mink.coneᶜ) v=0

theorem truth (p:Thirst P x): u.HauteTruth:=
 ⟨u.tucked p,u.haute.spacious (u.tucked p), fun x=>u.haute.basin (u.tucked p) x⟩

def Narrow:Prop:= 
 tsupport F.val ⊆ gate1.invites ∧ tsupport U.val ⊆ gate2.invites -- unused u
variable (e:P.ThinVelour x A c r n w)
local notation "Π"=> P.M4Velvet x A c r n
local notation "𝔸"=>foldSpace ⁻¹' gate1.invites
local notation "ℬ"=>foldSpace ⁻¹' gate2.invites
#print Narrow

lemma pockets (v:Π)(d:Narrow (F:=F) (U:=U))(a:C):
 u.garnet e a ∈ pocket Y 𝔸 ∧ u.peridot e a ∈ pocket Y ℬ:=by
  have q(W:SampleDose)(j:Set Vantage)(t:tsupport W.val⊆j):
    tsupport (sachet_LocalFieldBounds W) ⊆ foldSpace ⁻¹' j:= by rw [sachet_support];exact preimage_mono t
  have t:=u.iridescing_pocket v e a (q _ _ d.1)
  rw [sachet_bar] at t
  exact ⟨t,u.irising_pocket v e a (q _ _ d.2)⟩

theorem named_room (v:Π)(d:Narrow (F:=F) (U:=U))(p:Thirst P x)(a b:C):
  u.haute.Partner (u.garnet e a) (u.peridot e b):=
   (u.truth p).honest _ _
     (fun w t z g=>spacelike_reward w z (subset_closure t) (subset_closure g))
     (u.pockets e v d a).1 (u.pockets e v d b).2

#print axioms truth
#print axioms named_room


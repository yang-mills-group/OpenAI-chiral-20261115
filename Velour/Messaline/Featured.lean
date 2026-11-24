import Velour.Lustre.Renew

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 250000
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


variable (P x)
local notation "Y"=> P.glimmers x 3
local notation "M"=> Module.End ℂ D

/-- Enrich Latent with any Bobbin already effectively registered,
all supports, as operators on D. -/
def Stories: Set (P.Bobbin 3 ξ):=
 {a|∀f:Test4,θ a f∈pocket Y (tsupport f)}
abbrev Featured:=↥(P.Stories x)
def tells(i:P.Featured x):= θ i.val
def tellsEu(i:P.Featured x):= Q i.val
def features(u:P.Latent x): P.Featured x:=
 ⟨P.behold x 3 u, fun f=>show Y u f∈ pocket Y (tsupport f) from
  grove_seed u (P:=OS.Semigroup.placement (tsupport f)) (Set.Subset.refl _)⟩

lemma story_flip(i:P.Featured x):i.val.windBack∈P.Stories x:=by
 intro f
 obtain ⟨_,a,z,v⟩:= pocket_faces (P.meander x 3) (tsupport (bar f)) (i.property (bar f))
 have e: a = θ i.val.windBack (bar (bar f)):= v.unique (i.val.op_star (bar f))
 rw [show tsupport (bar f)=tsupport f by unfold tsupport;congr 1;ext; simp,
     e,show bar (bar f)=f from by ext;simp] at z
 exact z
 
lemma keepFray:(ℰ).Fray (P.tellsEu x) (P.tells x):=⟨
   fun i=>(P.satin_storage ..).1 i.val,
   fun i=>⟨⟨_,P.story_flip x i⟩,eventually_mem_nhdsWithin.mono (fun _ t=>i.val.backward t)⟩⟩


lemma story_grove(W:Set Test4)
 (k:∀f∈W,∀g:Test4, tsupport g⊆tsupport f → g∈W):
 (ℰ).grove (P.tells x) W=(ℰ).grove Y W:=by
 apply le_antisymm
 · refine Algebra.adjoin_le ?_
   rintro _ ⟨i,f,t,rfl⟩
   exact grove_mono (show OS.Semigroup.placement (tsupport f)⊆W from fun _=>k f t _) (i.property f)
 refine Algebra.adjoin_le ?_
 rintro _ ⟨i,f,t,rfl⟩
 exact grove_seed (P.features x i) t (T:=P.tells x)

lemma story_pocket (E:Set E4):
 pocket (P.tells x) E=pocket Y E:= P.story_grove x _ (fun _ t _ v=>Subset.trans v t)

lemma story_sprout:
  (ℰ).sprout (P.tells x) Ω=(ℰ).sprout Y Ω:=by
 have q:=P.story_grove x {f| OS.Semigroup.LocalTest f} (fun f t g v=>
    (show IsCompact (tsupport f) from t).of_isClosed_subset (isClosed_tsupport _) v)
 apply Submodule.ext; intro i
 change (∃a∈(ℰ).grove (P.tells x) {f|OS.Semigroup.LocalTest f},a Ω=i) ↔ (∃a∈(ℰ).grove Y {f|OS.Semigroup.LocalTest f},a Ω=i)
 rw [q]


lemma story_nursery: 
 (ℰ).nursery (P.tells x) Ω=(ℰ).nursery Y Ω:=congrArg (ℰ).district (P.story_sprout x)

variable {P x}
/-- All actual prices in particular, are in this enriched Fray. -/
def M4Furnish.featured (u:𝓕₄)(e:γ)(v:P.M4Velvet x A c r n)(a:C): P.Featured x:=
   ⟨u.violet e a, fun _=> u.irising_pocket v e a (Subset.refl _)⟩

#print axioms story_nursery


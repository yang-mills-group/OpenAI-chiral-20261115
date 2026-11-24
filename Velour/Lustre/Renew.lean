import Velour.Wadding.Violet
import Velour.Lustre.Meander
import Velour.Lustre.Ferrule
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

local notation "L"=> P.glimmers x 3
local notation "Π"=> P.M4Velvet x A c r n
def filament (_:𝓕₄) (v:Π) : P.Latent x:= ⟨A,v.cup⟩

/-- On **all of D**: actual violet detector recovered from a gauge clover
detector on a support-preserving transformed test. -/
theorem irising (u:𝓕₄)(v:Π) (e:γ)(a:C)(f:Test4):
 θ (u.violet e a) f=L (u.filament v) (fringed 3 (w a) (purePrice a) f):=by
 have y:P.Veloured 3 ξ A:=v.cup 3 []
 have p:= (P.combed_night a x A X v.handle y w u.experiment).1
 ext1 m; apply Subtype.ext
 apply tendsto_nhds_unique (((P.satin_storage 3 ξ).1 (u.violet e a)).meet f m)
 refine (((P.meander x 3).1 (u.filament v)).meet (fringed 3 (w a) (purePrice a) f) m).congr' ?_
 filter_upwards [self_mem_nhdsWithin] with d q
 change (ℰ).rasp (y.adorning d) _ _=(ℰ).rasp ((e a).adorning d) f m.val
 rw [←y.fringed_combs _ _ d (show 0<d from q) f]
 exact congrArg (fun t:(ℋ).Op=> (ℰ).rasp (P.tableau _ _ 0 t) f m.val) (p.dyes q).symm


theorem iridescing (u:𝓕₄)(v:Π) (e:γ)(a:C)(f:Test4):
 θ (u.violet e a).windBack (bar f)=
   L (P.sheens x (u.filament v) [3]) (bar (fringed 3 (w a) (purePrice a) f)):=by
   have q:=(u.violet e a).op_star f
   rw [u.irising v] at q
   exact q.unique (P.meander_faces x 3 (u.filament v) _)

lemma irising_pocket (u:𝓕₄)(v:Π) (e:γ)(a:C){f:Test4}{O:Set E4}
 (b:tsupport f⊆O) : θ (u.violet e a) f ∈ pocket L O:= by
 rw [u.irising v]
 exact grove_seed _ ((fringed_hem ..).trans b)

lemma iridescing_pocket (u:𝓕₄)(v:Π)(e:γ)(a:C){f:Test4}{O:Set E4}
 (b:tsupport f⊆O): θ (u.violet e a).windBack (bar f) ∈ pocket L O:=by
 rw [u.iridescing v]
 exact grove_seed _ (pocket_over ((fringed_hem ..).trans b))

theorem named_pockets (u:𝓕₄)(v:Π) (e:γ)(a:C):
 u.garnet e a ∈ pocket L (foldSpace ⁻¹' reviewEarlierBox.invites) ∧
 u.peridot e a ∈ pocket L (foldSpace ⁻¹' reviewLaterBox.invites):=by

 have b:tsupport (sachet_LocalFieldBounds F) ⊆ foldSpace ⁻¹' reviewEarlierBox.invites:=by
    rw [sachet_support]; exact preimage_mono u.boxF
 have t:tsupport (sachet_LocalFieldBounds U) ⊆ foldSpace ⁻¹' reviewLaterBox.invites:=by
    rw [sachet_support]; exact preimage_mono u.boxU
 have p:=u.iridescing_pocket v e a b
 rw [sachet_bar] at p
 exact ⟨p,u.irising_pocket v e a t⟩

#print axioms named_pockets



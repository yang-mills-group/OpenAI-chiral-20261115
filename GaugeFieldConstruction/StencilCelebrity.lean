import GaugeFieldConstruction.StencilOperatorInvoice
import GaugeFieldConstruction.StencilRope
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
open Calibration.Floor Calibration -- tune

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
open _root_.YM.SatinWFixed Carton InkPort
open _root_.YM.Boundary (Test4)
open _root_.YM.SatinRegistration
open NSF.Boundary
variable
  {nLeaf : ℕ}
  {process : Spine}
  {scale : process.Register}
  {production : YardμN process CostUpVU PolRun PriceArtVU nLeaf}
  {growth : InterR}
  {roles : ConsoleθN production ΓmotVU 0 growth ΓstageVU}
  {axes : Axis → GaugeFieldConstruction.Empire.Across}
  {comparison : Sheds roles.Crew_N axes}
  {approvals : Supplies comparison}
  {stress : Ticket roles.Gamma_N approvals}
  {vacuum : process.Spectrum0 3}
  {costAnalysis : process.Ellis 3 vacuum}
  {c : ℕ → ℕ}
  {collars : ℕ→ℕ}
  {layers : NSF.Boundary.Waves (roles.RadianceVU stress)}
  {response : NSF.Boundary.Surface (roles.RadianceVU stress)}
  {continued : NSF.Boundary.Surface.Aurora response NSF.LD.drapeL}
  {model : roles.GlowVU stress vacuum (le_refl _) layers response}
  {screens : process.Poll 3}
local notation "lab$" => (roles.RadianceVU stress).Union
open _root_.YM.Boundary (Joint Test4)
open OS.Semigroup
open Carton
local notation "ink"=> appointedLibrarySt model
local notation "TΔ"=> process.seasons 3 (process.advocate 3 vacuum 3)
local notation "P#"=> (roles.PerD_VU stress (le_refl _)).TinCanL
local notation "ord"=> model.system.operators
variable (u:WordSeatSt model)
local notation "ℱ"=> (ord).field
local notation "W"=> (ord).omega
local notation "Φ" => (ord).domain
variable {V:Type*}[AddCommGroup V][Module ℂ V]
variable (G: Carton (process.seasons 3 (process.advocate 3 vacuum 3)) V) (X Y:Module.End ℂ model.system.operators.domain) (s t:V) (f g:Test4) (m τ:ℂ)
include u
local notation "J"=> G.operator s f
local notation "K"=> G.operator t g
local notation "σ"=> (W) -- Conn
lemma scaleFull_sendsSt (p:u.sends X ((G).operator s f)) : u.sends (m • X) ((G).operator (m • s) f):=by rw [map_smul]; exact u.sends_scale _ _ _ p
variable {F:InkWaves V} {Z:WView V} (z: InkPort G F Z) (hq:G.omega=process.heaven 3 (process.advocate 3 vacuum 3))
include z hq
lemma starsOneHead_st (q:u.sends X ((G).operator s f)): inner ℂ W (X W)= Z.expect [(s,f)]:=by
 let T₀:=process.heaven 3 (process.advocate 3 vacuum 3);
 rw [z.real_value]; refine (u.invoice _ _ q).trans ?_; have hz:(ink).row []=G.vacuum:= by apply Subtype.ext; exact hq.symm
 rw [hz]; rfl
lemma starsBothHead_st(q:u.sends X ((G).operator s f))(p:u.sends Y ((G).operator t g)): inner ℂ W ((X*Y) W)= Z.expect [(s,f),(t,g)]:=by
 let T₀:=process.heaven 3 (process.advocate 3 vacuum 3);
 rw [z.real_value]; refine (u.invoice _ _ (u.sends_prod _ _ _ _ q p)).trans ?_; have hz:(ink).row []=G.vacuum:= by apply Subtype.ext; exact hq.symm
 rw [hz]; rfl
omit z
lemma veer_vacuSt (q:u.sends X ((G).operator s f))(p:u.sends Y ((G).operator t g))(hXY: Commute X Y) : (((G).operator s f)*((G).operator t g)) G.vacuum= (((G).operator t g)*((G).operator s f)) G.vacuum:=by
 have hs:(ink).row []=G.vacuum:=by apply Subtype.ext; exact hq.symm
 have hw:u.pocket σ =(ink).row []:= u.litPage []
 rw [←hs, ←hw]; exact (u.via_cash _ _ (u.sends_prod _ _ _ _ q p) σ).symm.trans ((congrArg u.pocket (DFunLike.congr_fun hXY.eq σ)).trans (u.via_cash _ _ (u.sends_prod _ _ _ _ p q) σ))
omit hq u
lemma localMoveHead_st (q:lab$)(A:Axis→(roles.RadianceVU stress).Union) (hp:NSF.Boundary.Fields.causal f g) : Commute (m • model.system.operators.field q f) (τ • ∑ j:Axis,model.system.operators.field (A j) (takeDerivative j g)) := by
 apply Commute.smul_left; apply Commute.smul_right; refine Commute.sum_right _ _ _ ?_; intro i _; apply LinearMap.ext; intro x; exact model.course.localPairs q (A i) f (takeDerivative i g) (fun x p y h => hp x p y (take_feet i g h)) x
#check @scaleFull_sendsSt
#check @starsOneHead_st
#check @starsBothHead_st
#check @localMoveHead_st
#check @veer_vacuSt
#print axioms starsBothHead_st
#print axioms scaleFull_sendsSt
#print axioms veer_vacuSt
end ContinuumConstruction
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end

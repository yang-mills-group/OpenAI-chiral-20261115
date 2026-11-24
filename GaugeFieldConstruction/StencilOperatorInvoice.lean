import GaugeFieldConstruction.StencilFrame
import GaugeFieldConstruction.StencilPanorama
import GaugeFieldConstruction.StencilEuWorld

/-! Identity of ordered readings on this seat, for any insertions actually proved to match. Useful for the retarding labels & station. -/
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
-- stronger than firmness of all axes. All orientation-qualified moments through only the time-3 space. Stamp positive waits. Applies to *any* such model.
open YM.CF.Buffered.Afterglow.Hierarchy
open YM.CF.Buffered.Afterglow.Hierarchy.Seld
include u
lemma pledge_at3_st (v:UV four)(p:∀ (l:PermWallJ process), projectLine process 3 vacuum (roles.RoomsVU v 3 l l)=0): v=0:=by
 let P:= (P#); let T:= (ord).field; let B:= ink
 have hz(t:ℝ≥0) (x:0<t): B.bar t (P v)=0:=by
    change StampShelf process vacuum roles.RoomsVU (PaidPadL process) (roles.PerD_VU stress (le_refl _)) t (P v) = 0
    rw [stamp_part _ _ _ _ _ _ _ x,P.symm_apply_apply v,p]; unfold sand; rw [mul_zero,zero_mul]
 have h(f:Test4)(z:radial TΔ): B.operator (P v) f z=0:=by
    apply Subtype.ext
    refine tendsto_nhds_unique_of_eventuallyEq (B.watches (P v) z f) tendsto_const_nhds ?_
    filter_upwards [self_mem_nhdsWithin] with i p; change valise (TΔ) (B.bar i (P v)) f z.val=0; rw [hz _ p]
    have he:= norm_le_zero_iff.mp ((Seld.vnorm (TΔ) 0 f).trans_eq (by rw [norm_zero,mul_zero])); rw[he]; rfl
 by_contra e; obtain ⟨f,j⟩:= model.course.faithful _ ((LinearEquiv.map_ne_zero_iff ..).mpr e : P v≠0)
 apply j; apply LinearMap.ext; intro x; apply u.pocket.injective; change u.pocket (T _ _ x)=u.pocket 0; rw [u.via_cash _ _ (u.sends_at (P v) f (J:=B.operator _ f) rfl)]; exact (h _ _).trans (map_zero u.pocket).symm
variable {V:Type*}[AddCommGroup V][Module ℂ V]
variable (G: Carton (process.seasons 3 (process.advocate 3 vacuum 3)) V)
omit u
lemma prices_by_bar_st (x:UV four)(y:V) (p:∀ t>0,(ink).bar t ((P#) x)= G.bar t y)(f:Test4) : G.operator y f= (ink).operator ((P#) x) f:=by
 apply LinearMap.ext; intro z; apply Subtype.ext; apply tendsto_nhds_unique_of_eventuallyEq (G.watches y z f) ((ink).watches _ z f); filter_upwards [self_mem_nhdsWithin] with i z'; erw [p i z'] -- semireducible barrier
include u
lemma preserve_by_bar_st (x:UV four)(y:V) (p:∀ t>0,(ink).bar t ((P#) x)= G.bar t y)(f:Test4) : u.sends ((ord).field ((P#) x) f) (G.operator y f):= u.sends_at _ _ (prices_by_bar_st G x y p f)
variable (hg:G.omega=process.heaven 3 (process.advocate 3 vacuum 3))
abbrev soldInkSt (x:UV four)(p:V): Prop:= ∀ f:Test4, u.sends ((ord).field ((P#) x) f) (G.operator p f)
include hg
lemma intoStationSt (A:List (UV four × V × Test4))(h:∀ p∈A, soldInkSt u G p.1 p.2.1) :
 u.pocket ((ord).evaluates (A.map fun x=> ((P#) x.1,x.2.2)))= G.row (A.map fun x=> (x.2.1,x.2.2)):=by
 induction A with
 | nil=> exact (u.litPage []).trans (Subtype.ext hg.symm)
 | cons q T ih =>
    change u.pocket ((ord).field ((P#) q.1) q.2.2 ((ord).evaluates _) )= G.operator q.2.1 _ (G.row _); rw [u.via_cash _ _ (h q (List.mem_cons_self ..) q.2.2), ih (fun x e=> h x (List.mem_cons_of_mem q e))]; rfl -- tune
variable {F:InkWaves ((roles.RadianceVU stress).Union)}{W:WView ((roles.RadianceVU stress).Union)}(t:WordPlaceSt (model:=model) F W)
variable {F':InkWaves V}{W':WView V}(t':InkPort G F' W')
include t t'
lemma newIncomeSt (n:ℕ)(x:Fin n→UV four)(q:Fin n→ V)(H:∀ i, soldInkSt u G (x i) (q i)) :
 response.W n ((P#) ∘ x) = W'.W n q ∧
 ∀ z:NSF.Boundary.Times n,z∈NSF.Boundary.strict n→∀ p:NSF.Boundary.SpacePoints n,
   layers.F n z p ((P#) ∘ x) = F'.F n z p q:=by
 let v:=(P#) ∘ x; let L:= (t.2.2.2.1 n v); have p':u.pocket ((ord).omega)=G.row []:= (u.litPage []).trans (Subtype.ext hg.symm)
 have hF(f:Fin n→Test4) : response.W n v (Joint.materialize n f)= W'.W n q (Joint.materialize n f):=by
    let A:=List.ofFn fun i=>(v i,f i); let Z:= List.ofFn fun i=>(q i,f i)
    let Q:= List.ofFn fun i=> (x i,q i,f i); have he : u.pocket ((ord).evaluates A)= G.row Z:=by
       have hp := intoStationSt u G hg Q (by intro p h; obtain ⟨i,rfl⟩:= List.mem_ofFn.mp h; exact H i)
       rw [show Q.map (fun p=>( (P#) p.1,p.2.2)) =A from ?_, show Q.map (fun p=>(p.2.1,p.2.2))=Z from ?_] at hp; exact hp
       all_goals rw [show Q = _ from rfl,List.map_ofFn]; rfl
    rw [show response.W n v (Joint.materialize n f)=response.expect A from (NSF.Work.C29.expectOfFn response (fun i=>(v i,f i))).symm]; have h:= model.course.meets A; rw [←h]; change inner ℂ (ord).omega ((ord).evaluates A)= _; rw [← u.pocket.inner_map_map, p', he]; exact (t'.tensor q f).symm
 have he: response.W n v=W'.W n q:=by
    apply ContinuousLinearMap.ext_on (R₁:=ℂ) (s:=Set.range (YM.Boundary.Joint.materialize n)); · intro x; change x∈(Submodule.span ℂ _).topologicalClosure; rw[_root_.YM.Work.C25.answer n]; exact Submodule.mem_top
    rintro y ⟨f,rfl⟩; exact hF f
 refine ⟨he,fun z e p=>?_⟩
 let HW:= t.1
 change layers.F n z p v= _; rw [←L.1 z e p]; exact Euro.relative_ink_st HW.gap_cost HW.weighted HW.looks t'.gap_cost t'.weighted t'.looks HW.region t'.region v q (L.2.trans he) z _ e
omit hg t'
lemma stationedSt (x:UV four)(p:V)(H:soldInkSt u G x p)(w:∀ f:Test4,G.operator p f∈ Submodule.span ℂ (Set.range (ink).activate)): StationPaysSt (ink) G ((P#) x) p:=by
 let F:= (P#) x; let D:= G.operator p; let A(f):= (ord).field F f; let B:= (ink).operator F
 apply earn_station_st model.system.J t.2.1 _ p w; intro f z
 rw [← u.litPage z]; erw [← u.via_cash (A f) (D f) (H f), ← u.via_cash (A f) _ (u.sends_at F f (J:=B f) rfl)]
#print axioms soldInkSt
#print axioms newIncomeSt
#print axioms pledge_at3_st
end ContinuumConstruction
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end

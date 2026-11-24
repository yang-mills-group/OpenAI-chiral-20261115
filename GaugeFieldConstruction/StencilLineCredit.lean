import GaugeFieldConstruction.StencilOperatorInvoice
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
variable {V:Type*}[AddCommGroup V][Module ℂ V] (G:Carton (process.seasons 3 (process.advocate 3 vacuum 3)) V)
local notation "Ԕ"=> soldInkSt u G
section match_st
lemma charges_inkSt {x:UV four}{y:V}(p:soldInkSt u G x y)(w:ℂ):soldInkSt u G (w • x) (w • y):=by
 intro f; rw [map_smul,map_smul, map_smul G.operator]; exact u.sends_scale _ _ _ (p f) -- syntax
lemma sumCharges_st {x x':UV four}{y y':V}(p:soldInkSt u G x y)(q:soldInkSt u G x' y'):soldInkSt u G (x+x') (y+y'):=by intro f; rw[map_add,map_add,map_add G.operator]; exact u.sends_add _ _ _ _ (p f) (q f)
end match_st
lemma moneyMany_st {I:Type*}(i: Finset I)(x:I→UV four)(y:I→V)(h:∀ p∈i,soldInkSt u G (x p) (y p)): soldInkSt u G (∑ p∈i,x p) (∑ p∈i,y p):=by
 intro f; rw [map_sum,map_sum,map_sum G.operator,LinearMap.sum_apply,LinearMap.sum_apply]; exact u.sends_sum _ _ _ (fun j q=>h j q f)
lemma spanEnough_st (x:UV four)(p:V) (g:∀ t>0,(ink).bar t ((P#) x)= G.bar t p)(f:Test4): G.operator p f∈ Submodule.span ℂ (Set.range (ink).activate):=by rw [prices_by_bar_st G x _ g]; exact Submodule.subset_span (show _∈Set.range (ink).activate from ⟨(((P#) x),f),rfl⟩)
local notation "ą"=> Submodule.span ℂ (Set.range (ink).activate)
lemma soldSpan_st (x p:V)(f:Test4)(g:G.operator p f∈ Submodule.span ℂ (Set.range (ink).activate))(u:G.operator x f∈ą): G.operator (p+x) f∈ą:=by rw [map_add,LinearMap.add_apply]; exact Submodule.add_mem _ g u
lemma soldRate_st (x:V)(c:ℂ)(f:Test4)(g:G.operator x f∈ Submodule.span ℂ (Set.range (ink).activate)): G.operator (c • x) f∈ą:=by rw [map_smul,LinearMap.smul_apply]; exact Submodule.smul_mem _ _ g
lemma soldEnsemble_st {I:Type*}(i: Finset I)(x:I→V)(f:Test4)(h:∀ j∈i,G.operator (x j) f∈ Submodule.span ℂ (Set.range (ink).activate)): G.operator (∑ p∈i,x p) f∈ą:=by rw[map_sum,LinearMap.sum_apply]; exact Submodule.sum_mem _ h
#print axioms soldSpan_st
#print axioms moneyMany_st
end ContinuumConstruction
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end

import GaugeFieldConstruction.StencilDerives
import GaugeFieldConstruction.ContinuumGenerators
import GaugeFieldConstruction.StencilCelebrity
import GaugeFieldConstruction.StencilJoule
/- # Total stress with derived field. Cost helpers to speed election specialization. -/
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

-- no Truth Unit unless paying this y.C. Data.FACT.mu.LORE.
namespace GaugeLimitJoint
open StressLaw
open _root_.YM.GaugeFieldConstruction.Ember.Volumetric.FirstPackMars.StLaw
open _root_.YM.Boundary (Distn)
variable (h:Assembled (scale:=scale) (costAnalysis:=costAnalysis) (c:=c) (collars:=collars)
   (continued:=continued) (model:=model) (screens:=screens))
variable (X:Axis→UV four) (U₁:Axis→ℂ)(σ₁:ℂ)(X':Axis→UV three)(i:ℕ)
lemma clockStash_st (j:Axis): takeDerivative j= clockSign j • DmoveRT j:=by
 by_cases p:j=3
 · rw [p,takeDerivative,if_pos rfl]; change -(Complex.I • DmoveRT 3)=(-Complex.I) • (DmoveRT 3); exact (neg_smul ..).symm
 rw [takeDerivative,if_neg p,clockSign,if_neg p,neg_smul,one_smul]<;> rfl
local notation "MaskL"=> roles.PerD_VU stress (le_refl _)
local notation "Creator"=> derivativeCreator (MaskL) model.system X U₁
local notation "Π_d" n:max i:max V:max d:max=> (shiftWard («W»:=response) MaskL i X U₁ (V:Fin n→UV four) d)
local notation "cape" n:max i:max V:max d:max=> curtainWard («W»:=response) stress MaskL i X U₁ (V:Fin n→UV four) d
noncomputable abbrev FDirectionSt (v:Test4→ₗ[ℂ] (model.system.operators.domain→ₗ[ℂ] model.system.operators.domain)) (d:Axis):Prop:=
    (∀ U:Set E4,∀ f:Test4, tsupport f⊆ U→ v f ∈ LockerΛL model.system U) ∧
    (∀ y:model.system.operators.domain,∀ f:Test4,HasDerivAt (fun t:ℝ=> (DragΛL model.system model.course (Mink.Poincare.translation (t • basis d)) (v f) y).val)
       (((v (-(ΦshiftΛ (basis d) f))) y).val) 0) ∧
     ∀ n:ℕ,∀ L: Fin n→UV four,∀ i:Fin n,
    (∀ f: Fin n→Test4, operatorPays model.system (Function.update (wage model.system ((MaskL).TinCanL ∘ L) f) i (v (-ΦshiftΛ (basis d) (f i))))= (Π_d n i L d) (Joint.materialize n f)) ∧
     (∀ (b:Axis) (f: Fin (n+1)→Test4), (cape n i L d) b (Joint.materialize (n+1) f) = let Jf:=Function.update (wage model.system (addXRT i ((MaskL).TinCanL ∘ L) (TensorInTheory (stress:=stress) b d)) f) i.succ (v (f i.succ)); operatorPays model.system Jf - operatorPays model.system (Jf ∘ (τNearRT i).s)) ∧
    wageUnit i (Π_d n i L d) (cape n i L d) (-(Complex.I * (MinkΛM d:ℂ)))
include h
lemma tightCosts_st (d:Axis) : FDirectionSt (model:=model) X U₁ Creator d:=by
 let V:= generates h; let e:= V.ward
 refine ⟨?_,?_,?_⟩
 · intro U f p; rw [derivA]; apply Subalgebra.sum_mem; intro z _; refine Subalgebra.smul_mem _ (Algebra.subset_adjoin ?_) _ -- now apply to the actual stress labels
   exact ⟨_, DmoveRT z f,(SchwartzMap.tsupport_lineDerivOp_subset (basis z) f).trans p,rfl⟩
 · intro y f; exact weight_field MaskL X U₁ model.course d f y
 intro n L j; refine ⟨fun f=> (field_receipt MaskL j X U₁ L model.course d f).symm,fun b f=>?_,derive_wage stress MaskL j X U₁ L e d⟩
 rw [V.stress_label]; exact stress_comm stress MaskL j X U₁ L e d b f
#print axioms tightCosts_st
omit h
local notation "§"=> fun j:Axis=> roles.DeckLiftVU i (X' j)
noncomputable abbrev sellerSt(s:ℂ) : Test4 →ₗ[ℂ] (model.system.operators.domain →ₗ[ℂ] model.system.operators.domain):= (s:ℂ) • ∑ j:Axis,(model.system.operators.field ((roles.PerD_VU stress (le_refl _)).TinCanL (roles.DeckLiftVU i (X' j)))).comp (Discipline.takeDerivative j).toLinearMap
lemma ancestry_st : sellerSt (model:=model) X' i σ₁=DescendantSt (model:=model) i X' σ₁:=by unfold sellerSt DescendantSt; simp_rw [clockStash_st]; rfl
lemma stauCreator_st : sellerSt (model:=model) X' i σ₁= derivativeCreator MaskL model.system (§) (fun j=>σ₁*clockSign j):=by
 ext1 f; rw [derivA]; simp only [sellerSt,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply, ContinuousLinearMap.coe_coe,clockStash_st,ContinuousLinearMap.smul_apply, map_smul]; simp_rw[Finset.smul_sum, smul_smul]
#print axioms ancestry_st
#print axioms stauCreator_st
end GaugeLimitJoint
end ContinuumConstruction
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end

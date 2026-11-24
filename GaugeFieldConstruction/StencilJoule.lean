import GaugeFieldConstruction.StencilOnsetEra
import GaugeFieldConstruction.GlowShipPV
import GaugeFieldConstruction.StencilPeoria
/-!
 # A generic spin-current pool & Eu and Lor symmetry of the descendant (paperDerivativeSt sign convention).
 -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
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
-- Data telescope. Naming concordance through the flagship API (QFT: E to Story,
-- L & G to continuity, calendars to labels and paths).
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
open Reconstruction ConsoleθN
open NSF.Boundary
open YM.Boundary (Test4 Joint Distn)
open Stage Stage.Cell
namespace GaugeLimitJoint
variable (Certificate : Assembled (scale:=scale) (costAnalysis:=costAnalysis) (c:=c) (collars:=collars)
   (continued:=continued) (model:=model) (screens:=screens)) (k:ℕ) (X:Axis→UV three) (t:roles.LeaseVU k)

local notation "ord"=>model.system
local notation "Uζ"=>roles.PerD_VU stress (le_refl _)
noncomputable abbrev clockSign (j:Axis) :ℂ:= if j=3 then -(Complex.I) else -1
lemma clockWaveS_st (j:Axis): clockSign j= -(Wickγ j)⁻¹:=by
 by_cases h:j=timeAxis
 · rw[h]; simp [timeAxis, Wickγ, clockSign]
 have p:j≠3:=h; simp [Wickγ,clockSign,h,p]
noncomputable def paperDerivativeSt (i:Axis): Test4 →L[ℂ] Test4:= clockSign i • ΦpaySt i
noncomputable abbrev DescendantSt (h:ℂ):= h • ∑ i:Axis, (model.system.operators.field ((roles.PerD_VU stress (le_refl _)).TinCanL (roles.DeckLiftVU k (X i)))).comp (paperDerivativeSt i).toLinearMap
noncomputable abbrev ΦSlotSt (x: UV four):= model.system.operators.field ((roles.PerD_VU stress (le_refl _)).TinCanL x)
noncomputable abbrev JSlotSt' (i:Axis):= ΦSlotSt (model:=model) (roles.DeckLiftVU k (X i))
noncomputable abbrev UprightSlot_st (i:Axis):= (Wickγ i)⁻¹ • JSlotSt' (model:=model) k X i
local notation "Xψ" => JSlotSt' (model:=model) k X
local notation "Gμ"=> model.system.operators.field
local notation "νκ" => UprightSlot_st (model:=model) k X
local notation "V'" => (roles.BinSchVU k three t).c
local notation "FΛ" i:max=> roles.DeckLiftVU k (X i)
local notation "ZΞ"=> roles.χVX stress vacuum
variable (U:GlyphSt)(w:WithTypefaceSt (stress:=stress) (vacuum:=vacuum) U)(h:ℂ)
include t
private lemma berryCostsSt (Z:UV three): roles.DeckLiftVU k Z=LowIncPV ((V') Z):= Calibration.inject four ((roles.DeckPortVU k t Z).trans (LowFivePV _).symm)
lemma berryGo3St (Z:UV three): roles.DeckLiftVU k Z=Go3PV ((V') Z):= Calibration.inject four ((roles.DeckPortVU k t Z).trans (goes3PV _).symm)
noncomputable abbrev JAnchorSt : UV four:= ∑ i:Axis,U i ((roles.BinSchVU k three t).c (X i))
variable (H:looksVectorSt X)
omit t in
lemma descendant_price_st (f:Test4): DescendantSt (model:=model) k X h f= h • ∑ j:Axis, JSlotSt' (model:=model) k X j (paperDerivativeSt j f):=by simp only [DescendantSt,LinearMap.sum_apply,LinearMap.smul_apply]; rfl
private lemma ferryScrollSt (Z:UV three)(g:Mink.Lorentz): SpheruleL stress g (roles.DeckLiftVU k Z)= roles.DeckLiftVU k (ForecastLPV g Z):=by rw[berryCostsSt k t,takesGatePV,berryCostsSt k t,legFreePV]
include H
lemma euWireJ_st (s:SO)(z:Axis): compassPiMars stress s (roles.DeckLiftVU k (X z))=∑ j:Axis,parcelMars s.val j z • FΛ j:=by
 rw [berryCostsSt k t, arcE_st, ←coin_E_st, Stage.euVector_st _ _ z H]; simp_rw[map_sum,map_smul,berryCostsSt k t]
local notation "hUP"=> JAnchorSt (roles:=roles) k X t U
include Certificate
lemma upright_fee_st : properCurrentSt stress (roles.WorldMxVU stress) (Uζ) model.course (UprightSlot_st (model:=model) k X):=by
 intro g i f
 let A(i):=(Uζ).TinCanL ((Wickγ i)⁻¹ • (FΛ i))
 have he(i:Axis)(f): (Gμ) (A i) f=(νκ) i f:= by unfold A; rw[map_smul,map_smul]
 have hv: model.system.spin.rail g.Λ (A i)=∑ b:Axis,costΛ g.Λ⁻¹ i b • A b:=by
    have hw:SpheruleL stress g.Λ (roles.DeckLiftVU k (X i))=∑ j:Axis,σVecL g.Λ j i • roles.DeckLiftVU k (X j):=by
       rw [ferryScrollSt k t, Stage.properVector_st X H]; rw [map_sum]; simp_rw [map_smul]
    unfold A; rw [model.labels,SurfCheckL.KSpunL,map_smul,hw]; simp_rw [Finset.smul_sum,map_sum,map_smul]
    apply Finset.sum_congr rfl; intro a _; rw[smul_smul,MinkSwapPhaseΛ,smul_smul]
 rw [← he,MeadΛL,hv]; simp_rw [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,he]; rfl
lemma Mink_descendantSt (g:Mink.Poincare)(f:Test4): DragΛL model.system model.course g (DescendantSt (model:=model) k X h f)=DescendantSt (model:=model) k X h (Joint.push g f):=by
 have e(f:Test4): DescendantSt (model:=model) k X h f= (-h) • ∑ i:Axis,(νκ) i (ΦpaySt i f):=by
    rw [descendant_price_st,Finset.smul_sum,Finset.smul_sum]; refine Finset.sum_congr rfl fun x _ =>?_ ; change h • (JSlotSt' (model:=model) k X x) _ = (-h) • ((Wickγ x)⁻¹ • (JSlotSt' (model:=model) k X x) _) ; unfold paperDerivativeSt; rw [ContinuousLinearMap.smul_apply,map_smul,smul_smul,smul_smul,clockWaveS_st]; rw [mul_neg,neg_mul]
 rw [e,e]; exact diveScalarSt stress _ _ model.course _ _ _ f (upright_fee_st Certificate k X t H)
#print axioms Mink_descendantSt
omit H
include U w
lemma descendantLabel_st (h:ℂ) : ΦSlotSt (model:=model) (h • (JAnchorSt (roles:=roles) k X t U))=DescendantSt (model:=model) k X h:=by
 ext1 f; unfold ΦSlotSt; rw [descendant_price_st]
 simp only [JAnchorSt,JSlotSt',ΦSlotSt,map_sum,map_smul,LinearMap.smul_apply, LinearMap.sum_apply]; refine congrArg (h • ·) (Finset.sum_congr rfl (fun i hi=>?_)); unfold paperDerivativeSt; simp only [ContinuousLinearMap.smul_apply,clockWaveS_st]; rw [berryGo3St k t,ReadShiftSt Certificate U w]
lemma VoidJAnchor_st (x:Points 1): roles.χVX stress vacuum 1 x ![h • (JAnchorSt k X t U)] =0:=by
 let B:= ZΞ 1 x; let L:=B.toLinearMap ![hUP] 0
 have hx(b:ΧiMars): B ![b]=L b:= by unfold L; rw [MultilinearMap.toLinearMap_apply]; congr 1; ext1 i; fin_cases i; simp
 rw [(hx (h • hUP): ZΞ 1 x ![h • hUP]=_),map_smul,←hx]
 let T:= roles.WarmVU stress vacuum (le_refl _) Certificate.path.phase_costs Certificate.path.ward_oracle
 rw [show B ![hUP]=0 from (ZenAngleVoid_st T w.2 x),smul_zero]
include H
lemma euBeam_st (s:SO): compassPiMars stress s (h • JAnchorSt (roles:=roles) k X t U)=h • JAnchorSt k X t U:=by
 let T:= roles.WarmVU stress vacuum (le_refl _) Certificate.path.phase_costs Certificate.path.ward_oracle
 rw[map_smul]; refine congrArg (h • ·) (?_); exact orbitGuideSt (Λ:=fun i=>roles.DeckLiftVU k (X i)) s stress T (roles.RotatesΕVU stress vacuum Certificate.path.phase_costs) w.2 (fun i=>berryGo3St k t (X i)) (fun g i=>euWireJ_st k X t (stress:=stress) H g i)
#print axioms euBeam_st
#print axioms descendantLabel_st
#print axioms upright_fee_st
end GaugeLimitJoint
end ContinuumConstruction
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end

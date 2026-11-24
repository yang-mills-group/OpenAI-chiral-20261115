import Verts.Born
import AuroraB.Clot
import Minnow.Younger
import Acacia.Loom
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section

open Filter Function Set Metric MeasureTheory
open scoped Topology InnerProductSpace NNReal ComplexOrder BigOperators
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
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
namespace Spine
open Aria Casting Six
namespace Habitat
variable {P:Spine} {x:P.Spectrum0 3} {c r:ℕ→ℕ} {K:P.Register} {J:P.Ellis 3 x}
variable (B:P.Experiment K c r x J)(Z:Lead.Clan)
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "ω"=> P.colorZero 3 (P.otherSpectrum 3 3 x)
local notation "Ω"=> P.heaven 3 ξ
local notation "H"=> P.ManyF 3 ξ
local notation "G"=> P.ColorHil 3 (P.otherSpectrum 3 3 x)
namespace Hemlock
open PledgeT MiterT Broker Aloft
open Py.Rate.Pitching.Focus (Morn)
namespace AuroraB.Verts
open Calico _root_.Yoland
variable (d:ℕ)(C D:ℕ→ℕ→ℝ)
local notation "φ" s:max=> (P.macroStep s:ℂ)
local notation "χ" t:max=>P.singleState 3 t x
local notation "isp" v:max=>aislePt (3:Axis) v
local notation "kd" s:max=> offer_update P d C D s B Z
local notation "Τ" s:max => agent P d C D s B Z
local notation "X" s:max t:max n:max U:max=> schema B Z d C D s t n U
local notation "Ψ"=> P.seasons 3 ξ
local notation "Λ"=> P.wealth 3 ξ
open _root_.YM.Preen DoseTravel Tower.Reconstruction
variable (s t n m:ℕ)(w:ℝ)(i:Lead.Clan)
variable (U V:SampleDose)(h:claimV w U)(v: claimV w V)
local notation "𝕌"=>P.reflectTest 3
local notation "Zs"=> central P d s
variable (p: offer_update P d C D s B Z ≤ t)(k:offer_update P d C D s B i ≤ t)
variable (l:4*Hemlock.radius P d s ≤ w)(R:P.Test→ₗ[ℂ]ℂ)(g: Comparison P.calibration (P.singleState 3 t x) R)
include p k l g h v B
private lemma party : R (𝕌 (chunk B Z d C D s t U)*chunk B i d C D s t V)=0 ∧ R (chunk B Z d C D s t U)=0∧ R (𝕌 (chunk B Z d C D s t U))=0:=by
 let C0:=P.comparator t x; have hm:=C0.choose_spec
 let T:= (Τ s); let S:=agent P d C D s B i
 have he:MatterWard P.calibration R:= Comparison.unique _ _ hm.1 g ▸ hm.2.2.2
 have hu:= (deputized P d C D s B Z).coordinates
 have hz:= (deputized P d C D s B i).coordinates
 refine ⟨swart T S t p k _ _ R g.1 he (fun a ha b hb=>?_),(Τ s).foresee t p _ R g.1 he,(Τ s).foresF t p _ R g.1 he⟩
 have hv':=v _ (pay_shift V (Zs) ((P.usedPose ..).mp ha))
 have hu':=h _ (pay_shift U (Zs) ((P.usedPose ..).mp hb))
 apply Set.disjoint_left.mpr; intro y q z
 have e0:=(abs_le.mp (S.location_leg t a k hz z 3)).1; have e1:=(abs_le.mp (T.location_leg t b p hu (P.mirror_back_pin t _ 3 q) 3)).1
 rw [show mirrorΩ _ y 3= -y 3 from if_pos rfl] at e1; linarith only [e0,e1,l,hu',hv']
#print axioms party
lemma voider: R (𝕌 (X s t n U)*schema B i d C D s t m V)=0 ∧ R (𝕌 (X s t n U))=0 ∧ R (schema B i d C D s t m V)=0:=by
 let z:= (P.macroStep s)
 let V'(A:SampleDose):=shuf A z
 induction n generalizing U with
 | zero=> induction m generalizing V with
    | zero=>
       have ha:=party B Z d C D s t w i U V h v p k l R g; have hb:=party B i d C D s t w i V V v v k k l R g
       exact ⟨ha.1,ha.2.2,hb.2.1⟩
    | succ m ih=>
       have ha:=ih V v; have hb:=ih _ (Shuffled V v z (P.macroStep_pos s).le)
       rw [rSchema, Algebra.mul_smul_comm,mul_sub,map_smul,map_sub,hb.1,ha.1,sub_zero,smul_zero, map_smul,map_sub,hb.2.2,ha.2.2,sub_zero,smul_zero]; exact ⟨rfl,ha.2.1,rfl⟩
 | succ n ih=>
    have ha:=ih U h; have hb:=ih _ (Shuffled U h z (P.macroStep_pos s).le)
    rw [rSchema,P.scale_mirror,map_sub,smul_mul_assoc,_root_.sub_mul,map_smul,map_sub,ha.1,hb.1,sub_zero,smul_zero,map_smul,map_sub,ha.2.1,hb.2.1,sub_zero,smul_zero]; exact ⟨rfl,rfl,ha.2.2⟩
#print axioms voider
#check @party
end AuroraB.Verts
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

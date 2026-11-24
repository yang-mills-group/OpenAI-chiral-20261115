import AuroraB.Helict
import AuroraB.Clockw
import AuroraB.Xphase
import SatinHeatSpecies
import AuroraB.Gill
import Mussel.Seal
import Mussel.Foil
import Mussel.Super
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
open PledgeT MiterT Broker
namespace AuroraB
open Tower.Reconstruction PledgeT MiterT Broker
variable (d:ℕ)(C D:ℕ→ℕ→ℝ)
local notation "Θ" s:max z:max=>offer_update P d C D s B z
local notation "aZ" s:max t:max i:max A:max=> schema B i d C D s t (score i) A
local notation "ϕ"=>P.reflectTest 3
local notation "𝕖" s:max i:max=> tiny (P:=P) d s (score i)
local notation "β"=>P.calibration
variable (s t:ℕ)(q:wide B d C D s t)
open Set
local notation "Hide" p:max s:max i:max=> {z:Vantage|∀ j:Axis,|z j - p j| ≤ 𝕖 s i}
-- Keep both source and receiving. flip
lemma hourQ(U:P.Test)(S:Set Vantage)(p:P.asked_at t U S)(v:U ∈ enclave β): P.asked_at t (ϕ U) ((poseMirror 3) ⁻¹' S)∧ (ϕ U∈enclave β):=by
 obtain ⟨A,g,e⟩:=p; exact ⟨⟨Tower.reflectedBox 3 0 A,P.canFlip _ _ g, fun _ h=>e (P.mirror_back_pin _ _ _ h)⟩,P.mirror_keeps _ _ v⟩ -- dots syntax
private lemma reflected(x:Vantage)(h:ℝ)(p:Vantage): (∀ i:Axis,|poseMirror 3 x i-p i|≤h) ↔ (∀i:Axis,|x i-poseMirror 3 p i|≤h):=by
 have e(i:Axis): |poseMirror 3 x i-p i|= |x i-poseMirror 3 p i|:=by
    change |mirrorΩ 3 x i - p i|=_; change _=|x i-mirrorΩ 3 p i|
    by_cases v:i=(3:Axis)<;>simp only [mirrorΩ,v,↓reduceIte]
    rw [show -x 3-p 3= -(x 3- -p 3) from by ring, abs_neg]
 simp_rw [e]
include q
lemma ready (U:SampleDose)(i:Cover)(p:i∈veil (P:=P) d s t U):
 let r:=macroZ B Z d C D s t (score Z) i
 let y:Vantage:=P.meshPose t i+central P d s
 y∈tsupport U.val ∧ P.asked_at t r (Hide y s Z) ∧ r∈enclave β ∧ P.asked_at t (ϕ r) (Hide ((poseMirror 3 y)) s Z) ∧ (ϕ r)∈enclave β:=by
 intro r y
 refine ⟨pay_shift U (central P d s) ((P.usedPose ..).mp p),?_⟩
 let V:=oval B Z d C D s t (score Z) i
 have e:=ameter B Z d C D s t (score Z) i
 have he:P.asked_at t r (Hide y s Z):=⟨V,e.1,fun _ h j=>legs B Z d C D s t q.1 (q.2 _) _ _ h j⟩
 obtain ⟨v,g⟩:=hourQ (P:=P) t r _ he e.2
 rw [show (poseMirror 3 ⁻¹' (Hide y s Z))= Hide (poseMirror 3 y) s Z from Set.ext (fun _=> reflected ..)] at v
 exact ⟨he,e.2,v,g⟩
set_option maxHeartbeats 430000 in
lemma shroud (U:SampleDose): ∃ (S:Finset Cover), (aZ s t Z U)∈ bay P.calibration S true ∧ P.pinFoot t S⊆ {y|∃v∈tsupport U.val, y∈Hide v s Z} ∧ aZ s t Z U ∈ enclave β:=by
 rw [face_in B Z d C D s t q.1]; let fx:=veil (P:=P) d s t U; let F(i:Cover):=oval B Z d C D s t (score Z) i; let S:= fx.biUnion F
 let R(i:Cover):=macroZ B Z d C D s t (score Z) i; let C':=bay β S true; let E':=enclave β
 have e(i:Cover) : R i ∈ bay β (F i) true∧R i∈E':=ameter B Z d C D s t _ i
 refine ⟨S,C'.sum_mem (fun i h=> C'.smul_mem (tallerBay β _ _ (subset_biUnion_of_mem F h) (e i).1) _),?_, E'.sum_mem (fun i _=> E'.smul_mem (e i).2 _)⟩
 rintro y ⟨j,h,t⟩; obtain ⟨i,r,x⟩:= Finset.mem_biUnion.mp (show j∈ S from h)
 exact ⟨P.meshPose _ i+central P d s,(ready B Z d C D s _ q U i r).1,fun k=> legs B Z d C D s _ q.1 (q.2 _) _ _ ⟨_,x,t⟩ k⟩
omit q
lemma h_tiny:Tendsto (fun s:ℕ=> tiny (P:=P) d s (score Z)) atTop (𝓝 0):= by simpa only [mul_zero,add_zero,tiny] using (((radiusTiny P d).const_mul 4).add ((P.macroStep_zero).const_mul (score Z:ℝ)))
#print axioms shroud
end AuroraB
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

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
open PledgeT MiterT Broker
open Tower.Reconstruction
variable {W Y:Bool}{u v:ℕ}(D:FrameZ P W u)(A:FrameZ P Y v)(t:ℕ)
local notation "L"=> P.calibration
-- t coexist >= k,ℓ components separated from mirrored exposure. buy.
set_option maxHeartbeats 600000 in
lemma loot (p:v ≤ t)(d i:Cover)(h:Disjoint (P.pinFoot t (Tower.reflectedBox 3 0 (D.swept t d))) (P.pinFoot t (A.swept t i))) (X:P.Test→ₗ[ℂ]ℂ) (q:Factors (L) X)(c:MatterWard (L) X):
 X (P.reflectTest 3 (Broker.pilot P u t d D.question) * Broker.pilot P v t i A.question)=0:= by
 let J:=P.reflectTest 3 (Broker.pilot P u t d D.question); let S:=Broker.pilot P v t i A.mainStem; let T:=Broker.pilot P v t i A.tailZ
 let E':= P.pinFoot t
 let A':=fence P v t i A.S0; let B':=fence P v t i A.T0; let H':=Tower.reflectedBox 3 0 (D.swept t d)
 let M:=H'∪A'
 have hs:J*S∈ bay (L) M true:= Subalgebra.mul_mem _ (tallerBay (L) _ _ subset_union_left (P.canFlip (D.swept t d) 3 (D.in_sweep t d))) (tallerBay (L) _ _ subset_union_right (tram v t i A.mainPin))
 have hw: Disjoint (E' B') (E' M):=by
   apply Set.disjoint_left.mpr; rintro z e ⟨r,f,u⟩; rcases Finset.mem_union.mp f with f|f
   · exact Set.disjoint_left.mp h (show z∈E' H' from ⟨_,f,u⟩) (P.pin_mono t _ _ (A.in_big t i) e)
   exact Set.disjoint_left.mp (A.pin_commission t i p) ⟨_,f,u⟩ e
 have hT:X (T*(J*S))=0:= P.far_price Y t _ _ q (.inl c) (Broker.commute Y v t i A.tailSense p) hs hw
 rw [A.fullID t i]; change X (J*(S*T))=0
 rwa [←mul_assoc,mul_comm (J*S)]
lemma swart(p:u ≤ t)(h:v ≤ t)(E F:SampleDose)(Q:P.Test→ₗ[ℂ]ℂ)(g:Factors L Q)(e:MatterWard L Q)
 (d:∀ i∈P.usedGrid t F,∀ j∈P.usedGrid t E,Disjoint (P.pinFoot t (Tower.reflectedBox 3 0 (D.swept t j))) (P.pinFoot t (A.swept t i))): Q (P.reflectTest 3 (D.batch t E)*A.batch t F)=0:=by
 unfold FrameZ.batch
 rw [map_sum,Finset.sum_mul,map_sum]
 refine sum_eq_zero fun j q=>?_; rw [Finset.mul_sum,map_sum]; refine sum_eq_zero fun i k=>?_
 rw [P.scale_mirror,smul_mul_assoc,mul_smul_comm,map_smul,map_smul,loot D A t h j i (d i k _ q) Q g e,smul_zero,smul_zero]
-- primary chunk props even arbitrary ts.D.Brand
variable (T:ℕ)(C D0:ℕ→ℕ→ℝ)(o:ℕ)(E F:SampleDose)(Zx:Lead.Clan)
local notation "Fw"=> agent P T C D0 o B Z
local notation "Gw"=> agent P T C D0 o B Zx
local notation "qz"=>offer_update P T C D0 o B Z
local notation "qx"=>offer_update P T C D0 o B Zx
local notation "Aw"=>central P T o
lemma fare3(p:qz ≤ t)(h:qx ≤ t) (t0:4*Hemlock.radius P T o  ≤ 1)(hp:∀ y∈tsupport E.val,(1:ℝ)<y 3)(hq:∀ y∈tsupport F.val,(1:ℝ)<y 3)(Q:P.Test→ₗ[ℂ]ℂ)(g:Factors L Q)(e:MatterWard L Q): Q (P.reflectTest 3 (chunk B Z T C D0 o t E)*chunk B Zx T C D0 o t F)=0:=by
 apply swart Fw Gw t p h _ _ Q g e; intro i hi j hj
 have h0:= pay_shift F (Aw) ((P.usedPose ..).mp hi); have h1:=pay_shift E (Aw) ((P.usedPose ..).mp hj)
 apply Set.disjoint_left.mpr; intro z v u
 have he:= abs_le.mp ((Gw).location_leg t i h (deputized P T C D0 o B Zx).coordinates u 3)
 have hh:= (abs_le.mp ((Fw).location_leg t j p (deputized P T C D0 o B Z).coordinates (P.mirror_back_pin t _ 3 v) 3)).1
 have ht:=hp _ h1; have hg:=hq _ h0
 rw [show mirrorΩ _ z 3= -z 3 from if_pos rfl] at hh; linarith only [he.1, hh,t0,ht,hg]
#print axioms fare3
end AuroraB
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

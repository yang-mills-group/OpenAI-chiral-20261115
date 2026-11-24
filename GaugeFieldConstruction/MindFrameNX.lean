import GaugeFieldConstruction.LargoKissNX
import GaugeFieldConstruction.TwilightStoryNX
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3400
set_option linter.unusedSectionVars false
set_option maxHeartbeats 85000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
namespace Spine
open Aria Set OS.Semigroup Ballad Six Glaze
open Papal FrameP Fock.Flux
variable (P:Spine)(j w:Fin 2){n:ℕ}(A:BeaconNX n)
variable (i:Axis)(a:ℤ)
open Lead Designs
lemma spinReturnPNX : shuffle i (shuffle i j)=j:=by fin_cases i<;>fin_cases j <;>decide
lemma pinClubNX : bkNX_scaledn i (shuffle i j)*bkNX_scaleup i j=(-1:ℂ)∧bkNX_scaleup i (shuffle i j)*bkNX_scaledn i j=(-1:ℂ):=by
 have he(p: SpinIdx):(∑ q:SpinIdx,pin i p q*pin i q p)=(-1:ℂ):= congrFun (congrFun (pin_square i) p) p|>.trans (by rw [Matrix.neg_apply,Matrix.one_apply_eq])
 constructor
 · have h:= he (upSpin j); rw [sum_eq_single (dnSpin (shuffle i j))] at h; swap
   · intro v _ p; rw [(bkNX_pinned i v j).1,if_neg p,mul_zero]
   swap; · simp
   unfold bkNX_scaledn bkNX_scaleup; rw [spinReturnPNX]; exact h
 have h:= he (dnSpin j); rw [sum_eq_single (upSpin (shuffle i j))] at h; swap
 · intro v _ p; rw [(bkNX_pinned i v j).2,if_neg p,mul_zero]
 swap; · simp
 unfold bkNX_scaledn bkNX_scaleup; rw [spinReturnPNX]; exact h
lemma turnReceiptNX: star (rotorCostNX i j w)*rotorCostNX i (shuffle i w) (shuffle i j)=(1:ℂ):=by
 rw [rotorCostNX,rotorCostNX,star_neg,star_mul,star_star]
 rw [show -(bkNX_scaleup i j*star (bkNX_scaledn i w)) * -(bkNX_scaledn i (shuffle i j)*star (bkNX_scaleup i (shuffle i w)))=(bkNX_scaledn i (shuffle i j)*bkNX_scaleup i j)*star (bkNX_scaleup i (shuffle i w)*bkNX_scaledn i w) from (by rw [star_mul]; ring)]
 rw[(pinClubNX j i).1,(pinClubNX w i).2]; simp
abbrev plaqueStakeNX (A: BeaconNX n): P.Test:= P.dressPuffNX A.1 A.2.1 A.2.2.1 A.2.2.2
abbrev flipBeaconNX:BeaconNX n:=(A.1.mirror i a,reverseRackNX A.2.1,shuffle i A.2.2.2,shuffle i A.2.2.1)
lemma flipColorBNX(K:Calibration): mirror K i a (Papal.household K (A.1.rollNX A.2.1 A.2.2.1 A.2.2.2))= rotorCostNX i A.2.2.1 A.2.2.2 • (Papal.household K ((A.1.mirror i a).rollNX (reverseRackNX A.2.1) (shuffle i A.2.2.2) (shuffle i A.2.2.1))):=funext (fun x=> (A.1.spectralRollNX A.2.1 A.2.2.1 A.2.2.2 i a (N:=K.c x)))
lemma gestureNX : P.reflectTest i (P.plaqueStakeNX A)= rotorCostNX i A.2.2.1 A.2.2.2 • P.plaqueStakeNX (flipBeaconNX A i 0):=Subtype.ext (flipColorBNX ..) -- tune
abbrev runBeaconNX : BeaconNX n:= (roam A.1 i (P.crewB a),A.2)
lemma practiceBNX : P.shifts i a (P.plaqueStakeNX A)= P.plaqueStakeNX (P.runBeaconNX A i a):=by
 let B:=flipBeaconNX A i 0
 let C:=flipBeaconNX B i (P.crewB a)
 have he: C=P.runBeaconNX A i a:=by
   unfold C runBeaconNX B flipBeaconNX
   exact Prod.ext rfl (Prod.ext rfl (Prod.ext (spinReturnPNX ..) (spinReturnPNX ..)))
 rw [←he]; apply Subtype.ext
 let K:= P.calibration
 have hp(X:BeaconNX n)(a:ℤ): Tower.mirror K i a (P.plaqueStakeNX X).val= rotorCostNX i X.2.2.1 X.2.2.2 • (P.plaqueStakeNX (flipBeaconNX X i a)).val:= flipColorBNX ..
 change relocate K i a (P.plaqueStakeNX A).val=_
 have ht:P.crewB a-0=gaugeT K a:=sub_zero _
 rw [←mirror_at K i ht (P.plaqueStakeNX A).property,hp,mirror_scale,hp,smul_smul]
 rw [show _*_= _ from turnReceiptNX A.2.2.1 A.2.2.2 i,one_smul]
#print axioms practiceBNX
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end

import YM.SU5.Selected.FullLattice
/-!
# Tilted planar reflection of the FIELD labels and physical motion
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Tilted
open Function Fock Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase MeasureTheory RP Reflect Advance
  Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin SatinVerification
structure Ramp where
 a:Axis
 b:Axis
 cross:b≠a
namespace Ramp
variable (P:Ramp)
local notation "a" => P.a
local notation "b" => P.b

def s : Signed:=⟨Equiv.swap P.a P.b,fun i=>decide (i=P.a∨i=P.b)⟩
def plan:=incX P.s
@[simp] lemma sab:P.s.perm P.a=P.b:=by unfold s; exact Equiv.swap_apply_left ..
@[simp] lemma sba:P.s.perm P.b=P.a:=by unfold s; exact Equiv.swap_apply_right ..
@[simp] lemma saa {i:Axis}(x:i≠P.a)(y:i≠P.b):P.s.perm i=i:=Equiv.swap_apply_of_ne_of_ne x y
@[simp] lemma fee_a:P.s.flip P.a=true:=by simp [s]
@[simp] lemma fee_b:P.s.flip P.b=true:=by simp [s]
@[simp] lemma fee_h {i:Axis}(x:i≠P.a)(y:i≠P.b):P.s.flip i=false:=by simp [s,x,y]
lemma swing : P.s*P.s=1:=by
 apply Signed.ext; ext i : 1; change Equiv.swap P.a P.b (Equiv.swap P.a P.b i)=i; exact Equiv.swap_apply_self ..
 funext i; by_cases v:i=P.a; · subst i; simp
 by_cases e:i=P.b; · subst i; simp
 simp [v,e]
lemma replan: joinX P.plan P.plan=incX 1:=by simp [Ramp.plan,joinX,incX,P.swing] -- tune
lemma move_a {X : Type*}[AddGroup X] (x:Four X): P.s.act x P.a= -x P.b:=by simpa using P.s.act_at x P.b
lemma move_b {X : Type*}[AddGroup X] (x:Four X): P.s.act x P.b= -x P.a:=by simpa using P.s.act_at x P.a
lemma move_h {X : Type*}[AddGroup X] (x:Four X) {i:Axis} (u:i≠P.a)(v:i≠P.b): P.s.act x i= x i:=by simpa only [P.saa u v,P.fee_h u v,Bool.false_eq_true,ite_false] using P.s.act_at x i -- tune

-- Pin, with sign. Used simultaneously in every component of mark history.
lemma swaps_pin (i j:Axis) (p:i≠j) : pin i*pin j= -(pin j*pin i):= by
 unfold pin; simp only [←mul_assoc]; rw [mul_assoc (gammaOp i), gradingSwap, mul_neg, ←mul_assoc, neg_mul, gammaSwap i j p, neg_mul, neg_mul,neg_neg, mul_assoc (gammaOp j) grading, gradingSwap, mul_neg, neg_mul, neg_neg, mul_assoc]; simp only [mul_assoc]
-- references for spinL laws at both axes rotations
private def coeff:ℝ:=(Real.sqrt 2)⁻¹
def imageP(P:Ramp) : Op SpinIdx:= coeff • (pin P.a + pin P.b)
private lemma paysP: coeff*coeff=1/2:=by
 unfold coeff; rw [show (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹= (Real.sqrt 2*Real.sqrt 2)⁻¹ from (_root_.mul_inv_rev _ _).symm, Real.mul_self_sqrt (by norm_num), one_div]
lemma skew : star P.imageP= -P.imageP:=by
 unfold imageP; rw [star_smul,star_trivial,star_add,pinS,pinS, show -pin P.a + -pin P.b= -(pin a+pin b) by abel, smul_neg]
lemma squarish:P.imageP*P.imageP= -1:=by
 let F:=pin a+pin b
 have h:F*F= -1+(-1:Op SpinIdx):=by unfold F; rw [mul_add,add_mul,add_mul,pin_square,pin_square,swaps_pin a b P.cross.symm]; abel
 change (coeff • F)*(coeff • F)=_
 rw [Matrix.smul_mul,Matrix.mul_smul, h, smul_smul,paysP, smul_add,←add_smul]
 norm_num
noncomputable def reel:UNI SpinIdx:= ⟨P.imageP, Matrix.mem_unitaryGroup_iff.mpr (by change P.imageP*star _= _; rw [skew, mul_neg, squarish, neg_neg])⟩
private lemma together_neg (i j:Axis): (pin i+pin j)*gammaOp j= (-gammaOp i)*(pin i+pin j):=by
 unfold pin; rw [add_mul,mul_add,mul_assoc,mul_assoc,gradingSwap,mul_neg,mul_neg,neg_mul,neg_mul]
 simp only [←mul_assoc, gammaOne]
 rw [add_comm]
private lemma together_no (i j:Axis)(p:j≠i): pin i* gammaOp j= gammaOp j* pin i :=by rw [pin,mul_assoc,gradingSwap,mul_neg,←mul_assoc,gammaSwap i j p.symm,neg_mul,neg_neg,mul_assoc]
lemma jet: JetS P.s false true P.reel:= by
 refine ⟨fun i=>twist_comm _ _ _ ?_,twist_comm _ _ _ ?_,?_⟩
 · change P.imageP * gammaOp (P.s.perm i) =hush _ _ * P.imageP
   unfold imageP; rw [Matrix.smul_mul,Matrix.mul_smul]; apply congrArg
   by_cases x:i=a; · subst i; rw [P.sab,P.fee_a,hush_true]; exact together_neg a b
   by_cases y:i=b; · subst i; rw [P.sba,P.fee_b,hush_true, add_comm (pin a)]; exact together_neg b a
   rw [P.saa x y,P.fee_h x y,hush_false,add_mul,mul_add,together_no a i x,together_no b i y]
 · change (P.imageP)*grading= (-grading)*P.imageP
   unfold imageP; rw [Matrix.smul_mul,Matrix.mul_smul, add_mul, mul_add]; have h (i:Axis): pin i*grading = (-grading)*pin i:=by rw [pin,neg_mul,←mul_assoc, gradingSwap,neg_mul,neg_neg]
   rw [h,h]
 change P.imageP*_= _*cc P.imageP; unfold imageP; rw [Matrix.smul_mul,cc_rsmul, Matrix.mul_smul, cc_add, add_mul,mul_add]; have h (i:Axis):pin i*spinJ=spinJ*cc (pin i):=(mirrorX i).justice
 rw [h,h]
lemma proper_pin : detX P.s=true:= mono_d P.s false true P.reel P.jet
lemma pin_a: P.imageP * pin P.a=pin P.b*P.imageP:=by unfold imageP; rw [Matrix.smul_mul,Matrix.mul_smul,add_mul,mul_add,pin_square,pin_square]; abel
lemma pin_b: P.imageP * pin P.b=pin P.a*P.imageP:=by unfold imageP; rw [Matrix.smul_mul,Matrix.mul_smul,add_mul,mul_add,pin_square,pin_square]; abel
lemma pin_z (i:Axis)(x:i≠a)(y:i≠b) : P.imageP * pin i= -(pin i * P.imageP):=by unfold imageP; rw [Matrix.smul_mul,Matrix.mul_smul, add_mul, mul_add,swaps_pin _ _ x.symm,swaps_pin _ _ y.symm]; simp only [smul_add,smul_neg]; abel
end Ramp
end YM.CF.Buffered.Afterglow.Tower.Tilted

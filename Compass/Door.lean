import YM.CF.Hove.Cite
import YM.CF.Hove.Canon
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Spin
import YM.CF.Hove.Prune
import Compass.Match
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Compass
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open Tap Hake Levier Hove
-- adapt Mantel. sign.
-- check base
open Nacre Ione
variable {N:Side}(A:Shape)(U:UNI SpinIdx)(p r: Bool)(t:JetS A.s p r U)
variable (o x:Site N)(h:10*separation x o < N.val)
lemma space_T (s:Signed)(i:Axis)(g:Cover) : ((s.act (g:Four ℤ) (s.perm i):ℤ):ℂ)=(↑(StressFlux.sign s i):ℂ)*(g i:ℤ):=by rw [Signed.act_at]; cases e:s.flip i <;> simp [StressFlux.sign,e]
-- ox,Lift
include h
lemma twist_lift : Lattice.lift (A.mills N x-A.mills N o)= A.s.act (Lattice.lift (x-o)):=by
 unfold Shape.mills affine; rw [add_sub_add_right_eq_sub,←Signed.act_sub]; apply lift_eq_iff.mpr
 refine ⟨?_,fun i=>?_⟩; rw [←wrap_signed,wrap_lift]
 obtain ⟨j,rfl⟩:= A.s.perm.surjective i
 have hi:= component_le (x-o) j; unfold separation at h; rw [Signed.act_at]; split<;> omega
lemma east_wind : Rush.wind (A.mills N o) (Lattice.lift (A.mills N x-A.mills N o))*A.payA x=A.payA o* Rush.wind o (Lattice.lift (x-o)):=by
 rw [twist_lift A o x h]
 have he:= footFee (a:=A) o (Lattice.lift (x-o))
 rw [wrap_lift,add_sub_cancel] at he
 -- he: pay o * old = new * pay x, implies pay x * old=new*pay o
 let i:= Lattice.lift (x-o); let f:= Rush.wind o i; let g:= Rush.wind (A.mills N o) (A.s.act i)
 change A.payA o*g=f*A.payA x at he
 change g*A.payA x=A.payA o*f
 rw [show g= A.payA o*(A.payA o*g) by rw [←mul_assoc,A.reflex,one_mul], he]
 calc
 _ = (A.payA o*f)*(A.payA x*A.payA x) := by ring
 _ = _ :=by rw [A.reflex,mul_one]
-- restricted matrix identity. complex smul signWind for r,p each rect
variable {a b:Type*}
def rectSign(q:Bool)(F:Matrix a b ℂ):Matrix a b ℂ:=Matrix.of (fun i j=>cSignX q (F i j))
omit h
lemma scaleT (a:ℂ)(M:Op Kt):sings p (twoU U p) (a•M)=cSignX p a • sings p (twoU U p) M:=by rw [singT,win_c,twist_scalar]; rfl
include t
lemma basePull (a:Bool) : sings p (twoU U p) (baseF a)= baseF (r.xor a):=by
 have hp (a:Bool): baseF a=(Fir.angle (!a)) ⊗ₖ (1:Op Slot):=by cases a; rfl; change (1-(Aop ⊗ₖ (1:Op Slot)))=(1-Aop) ⊗ₖ 1; rw [sub_eq_add_neg (1:Op SpinIdx),Matrix.add_kronecker, Matrix.one_kronecker_one,op_kron_neg]; rfl
 rw [hp,Scroll.wingK,angleX t, singT _ _ 1,win_i,map_one,hp,show r.xor (!a)=!(r.xor a) from by cases r<;>cases a<;>rfl]
lemma dit_pull (a:Bool)(k:Axis): sings p (twoU U p) (ditF a (A.s.perm k))= (↑(StressFlux.sign A.s k):ℂ) • ditF (r.xor a) k:=by
 have he (a:Bool)(i:Axis): ditF a i = (if a then (1/2:ℂ) else -1/2) • ((grading*gammaOp i) ⊗ₖ (1:Op Slot)):=by
    unfold ditF Tap.boom taxi; rw [show Fir.zen (step i)=Complex.I • gammaOp i from by unfold Fir.zen; rw [sum_eq_single i]; simp; intro _ _ h; simp [h]; simp,Matrix.mul_smul,smul_smul,Matrix.smul_kronecker] -- maybe name
    have hx:Complex.I * ((2:ℂ)⁻¹ *Complex.I)=-1/2:=by ring_nf; simp; ring
    cases a<;>simp [smul_smul,hx,neg_div]
 rw [he,scaleT U p, Scroll.wingK,singT p (xtra p).V 1,win_i,map_one,singT,win_m,map_mul,←singT,←singT,t.cliff,t.grade,he]
 cases p <;> cases a<;> cases r<;> cases z:A.s.flip k <;> simp [StressFlux.sign,z,cSignX,op_kron_neg]<;>module -- tune
end YM.CF.Compass

import YM.SU5.FiniteGaugeData.Hills.Enclave
import YM.CF.Buffered.Spun
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Nacre Heat Charm Chrono Journey
namespace Hills
section
open Mir
variable (a b:Axis)(p:a≠b) -- use z=0 only. general enough by translation or not need.Lic
private lemma jointC : joinX (plane a 0) (plane b 0) = joinX (plane b 0) (plane a 0):= by
 simp only [joinX,plane,zero_smul,Signed.act_zero,add_zero]; congr 1; apply Signed.ext; · rw [Signed.mul_perm,Signed.mul_perm]; rfl
 funext i; simp [Signed.mirror, Bool.xor_comm]; rfl
include p in
private lemma pp : pin a * pin b= -(pin b*pin a):= by
 rw [show pin b=gammaOp b*grading from rfl,←mul_assoc,Mil.mirror_others a b p,mul_assoc,Mil.anti,neg_mul,mul_neg,mul_assoc]
include p
private lemma mirror_C {N:Side} : (carR a 0 N).val*(carR b 0 N).val= -((carR b 0 N).val*(carR a 0 N).val):=by
 change (carR a 0 N *carR b 0 N).val= -(carR b 0 N * carR a 0 N).val; unfold carR; rw [kio,kio,jointC]
 let A':= pinLift b *pinLift a; have h: (pinLift a*pinLift b).val= (-1:ℂ) • A'.val:= by rw [neg_one_smul]; exact pp a b p
 rw [Ygs _ _ _ h,neg_one_smul]
omit p in
lemma theta_jump {I:Type*}[Fintype I][LinearOrder I]{s:Finset I}{T: FC I}(U V:UNI I)(p:U.val*V.val=-(V.val*U.val))(h:Sector s false T): theta U (theta V T)=theta V (theta U T):=by
 let A:= phaseU (I:=I) (-1) (by simp); let N:= V*U
 have he: (N*A).val= -N.val:= by change _* ((-1:ℂ) • (1:Op I))= _; rw [Algebra.mul_smul_comm,mul_one,neg_one_smul]
 rw [theta_theta U V N p h,theta_theta V U (N*A) (show _=-(N*A).val from by rw [he, neg_neg]; rfl) h, show quantU (N*A)=quantU N*quantU A from Subtype.ext (quant_mul ..), Fock.twin, h.grade_diag, if_neg (by decide : ¬ (false = true)),one_smul] -- notation he theta etc
lemma fire_pair (K:Calibration)(f:W K): fire K a 0 (fire K b 0 f)=fire K b 0 (fire K a 0 f):=by
 apply Subtype.ext; funext m i; unfold fire; change theta _ (theta _ (f.val m _))= theta _ (theta _ (f.val m _)); simp_rw [reflFields,Prod.map, fling,←kor,jointC b a]; exact theta_jump (carR a 0 _) _ (mirror_C a b p) (((well_for K f).1.paid.choose_spec.support m).allV _).sector
#print axioms fire_pair
end
end Hills
end YM.CF.Buffered.Afterglow.Hierarchy

import YM.SU5.Reconstruction.Oblique.Bows
/-! # signed action through Frame. Ensure compatibility with all stencil translation budgets when acting on the physical phase. -/
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
namespace Ramp
variable (P:Ramp) {N: Side}
local notation "T" => P.plan
lemma s_inv(P:Ramp):P.s⁻¹=P.s:=inv_eq_of_mul_eq_one_left P.swing
-- sign of offset
lemma join_pin (s:Signed)(i:Axis): Signed.mirror (s.perm i)*s = s*Signed.mirror i:=by
 apply Signed.ext; ext k : 1; simp [Signed.mirror]
 funext k; by_cases p:i=k; · subst i; simp [Signed.mirror, Bool.xor_comm]
 simp [Signed.mirror,p]
abbrev changeAxis (P:Ramp)(i:Axis):=P.s.perm i
lemma jog {X:Type*}[AddGroup X][One X](u: Signed)(j:Axis): u.act (step j : Four X)=if u.flip j then -(step (u.perm j)) else step (u.perm j):=by
 funext i
 obtain ⟨i,rfl⟩:=u.perm.surjective i; rw [Signed.act_at]; by_cases p:j=i; · subst i; split_ifs <;> simp
 cases h:u.flip j <;> simp [step_apply,p,Ne.symm p]
lemma jogAt(s:Signed)(i:Axis)(z:ℤ): s.act (z • (step i: Cover))=hush (s.flip i) z • step (s.perm i):=by
 rw [show s.act (z • (step i: Cover)) =z • s.act (step i) from map_zsmul (s.actEquiv (R:=ℤ)) ..,jog]; cases h:s.flip i <;> simp
lemma plan_pins(i:Axis)(z:ℤ): joinX (plane i z) T= joinX T (plane (P.s.perm i) (hush (P.s.flip i) z)):=by
 -- first plan then axis original. Need fixed P inverse & plane scored in reflection
 unfold joinX plane Ramp.plan incX; dsimp only
 have he:=join_pin P.s⁻¹ (P.s.perm i); simp only [Signed.inv_perm,Equiv.symm_apply_apply] at he
 rw [s_inv] at he; rw [he,Signed.act_zero, zero_add,add_zero]; congr 1
 rw [←jogAt,P.act_act]
lemma pathways (i:Axis)(z:ℤ)(V: Pane N) : fling i z N (P.turnLink N V)=P.turnLink N (fling (P.s.perm i) (hush (P.s.flip i) z) N V) := by
 unfold fling turnLink; rw [←kor,←kor]; apply congrArg (fun s=> Yg s V)
 -- RHS: joinX (plane ... ) T with i' ; inverse shape
 let k:= P.s.perm i; have hk : P.s.perm k=i:=by simpa using (congrArg (fun s:Signed=>s.perm i) P.swing)
 have he:=P.plan_pins k (hush (P.s.flip i) z)
 have h:P.s.flip k=P.s.flip i:= by
    unfold k; by_cases u:i=P.a; · rw [u,P.sab]; simp
    by_cases e:i=P.b; · rw [e,P.sba]; simp
    rw [P.saa u e]
 rw [hk,h,hush_comp,Bool.xor_self,hush_false] at he; exact he.symm
private lemma spin_shift_good(i:Axis)(z:ℤ)(p:P.imageP * pin i=pin (P.s.perm i)*P.imageP): P.vehicle N * carR i z N =carR (P.s.perm i) (hush (P.s.flip i) z) N* P.vehicle N:=by rw [vehicle,carR,carR,kio,kio,P.plan_pins,show P.reel*pinLift i= pinLift (P.s.perm i)*P.reel from Subtype.ext p]
private lemma spin_shift_flip(i:Axis)(z:ℤ)(p:P.imageP * pin i= -(pin (P.s.perm i)*P.imageP)): (P.vehicle N * carR i z N).val = - (carR (P.s.perm i) (hush (P.s.flip i) z) N* P.vehicle N).val:=by
 rw [vehicle,carR,carR,kio,kio,P.plan_pins]
 have h:(P.reel*pinLift i).val=(-1:ℂ) • (pinLift (P.s.perm i)*P.reel).val:=by rw [neg_one_smul]; exact p
 rw [Ygs _ _ _ h,neg_one_smul] -- proof bind
private lemma same_vehicle {I:Type*}[Fintype I][LinearOrder I](A B C D : UNI I)(k:A*B=C*D){S: Finset I}{v: Bool}{X:FC I}(p:Sector S v X): Fock.theta A (Fock.theta B X)=Fock.theta C (Fock.theta D X):=by
 have up(U V: UNI I)(i:I): Fock.theta U (Fock.theta V (put i))= -create (acts (U*V).val (basisKet i)):=by rw [theta_up,theta_smul,theta_downV,←act_mul]; simp [smul_smul]
 induction p with
 | zero=> simp only [theta_zero]
 | one=> simp only [theta_one]
 | up i _=> rw [up,up,k]
 | down i _=> rw [takeF, theta_star,theta_star,theta_star,theta_star,up,up,k]
 | mul _ _ u v=>rw [theta_mul,theta_mul,theta_mul,theta_mul,u,v]
 | add _ _ u v=>rw [theta_add,theta_add,theta_add,theta_add,u,v]
 | scale _ c u=> rw [theta_smul,theta_smul,theta_smul,theta_smul,u]
private lemma opposite_vehicle {I:Type*}[Fintype I][LinearOrder I](A B C D : UNI I)(k:(A*B).val= -(C*D).val){S: Finset I}{v: Bool}{X:FC I}(p:Sector S v X): Fock.theta A (Fock.theta B X)= (if v then (-1:ℂ) else 1) • Fock.theta C (Fock.theta D X):=by
 have up(U V: UNI I)(i:I): Fock.theta U (Fock.theta V (put i))= -create (acts (U*V).val (basisKet i)):=by rw [theta_up,theta_smul,theta_downV,←act_mul]; simp [smul_smul]
 induction p with
 | zero=> simp only [theta_zero,smul_zero]
 | one=> rw [theta_one,theta_one,theta_one,theta_one]; simp
 | up i _=> rw [up,up,k,act_neg,map_neg]; simp
 | down i _=> rw [takeF, theta_star,theta_star,theta_star,theta_star,up,up,k,act_neg,map_neg]; simp
 | @mul i j _ _ x y u v=>rw [theta_mul,theta_mul,theta_mul,theta_mul,u,v]; cases i <;> cases j <;> simp
 | add _ _ u v=>rw [theta_add,theta_add,theta_add,theta_add,u,v,smul_add]
 | scale _ c u=> rw [theta_smul,theta_smul,theta_smul,theta_smul,star_star,u,smul_comm]
lemma tilt_pair(i:Axis)(z:ℤ){S:Support (More N)}{x:Mark N}(p:AtSupport false S x): P.bill (reflMark i z x)= reflMark (P.s.perm i) (hush (P.s.flip i) z) (P.bill x):=by
 funext y; let v:=P.both N (reflFields (P.s.perm i) (hush (P.s.flip i) z) y); have ht:reflFields i z (P.both N y)=v:=Prod.ext (P.pathways i z _) (P.pathways i z _)
 unfold bill reflMark; rw [ht]
 apply Or.elim (a:=P.imageP*pin i=pin (P.s.perm i)*P.imageP) (b:=P.imageP*pin i= -(pin (P.s.perm i)*P.imageP)) ?_
    (fun h=>same_vehicle _ _ _ _ (P.spin_shift_good i z h) (p.allV v).sector) (fun h=>by simpa only [Bool.false_eq_true,ite_false,one_smul] using opposite_vehicle _ _ _ _ (P.spin_shift_flip i z h) (p.allV v).sector)
 by_cases q:i=P.a; · subst i; rw [P.sab]; exact Or.inl P.pin_a
 by_cases r:i=P.b; · subst i; rw [P.sba]; exact Or.inl P.pin_b
 rw [P.saa q r]; exact Or.inr (P.pin_z i q r)
lemma sees (J:Calibration){x:Family J}(p:TestFamily J true x)(i:Axis)(z:ℤ): P.cuspF J (mirror J i z x) = mirror J (P.s.perm i) (hush (P.s.flip i) z) (P.cuspF J x):=funext fun m=> P.tilt_pair i z (p.paid.choose_spec.support m)
end Ramp
end YM.CF.Buffered.Afterglow.Tower.Tilted

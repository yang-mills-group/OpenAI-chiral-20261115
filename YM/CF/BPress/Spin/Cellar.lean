import YM.CF.BPress.Spin.Grading
import Mathlib.Analysis.CStarAlgebra.Projection
/-! Conditioning matrix pencil (eq:B-Suw) as far as entering columns. Traces and
 optional insertions use only the tilted projector as argument, here written A general. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Spin
open Function Filter NormedSpace Finset Fock Branch Quad Dial Pledge
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
namespace Cellar
variable {I:Type}[Fintype I][DecidableEq I][Nonempty I]{c:ℝ}{A P Q R L D:Op I}
lemma backJ (p:IsSelfAdjoint A)(q:IsSelfAdjoint P)(r:IsSelfAdjoint L)(h:A*P=L) : P*A=L:=by have he:= congrArg star h; rwa [star_mul,p,q,r] at he
lemma back (p:IsStarProjection A)(q:IsStarProjection P)(h:A*P=0): P*A=0:= backJ p.isSelfAdjoint q.isSelfAdjoint (show IsSelfAdjoint (0:Op I) from star_zero _) h -- tune
lemma across (p:IsStarProjection A)(q:IsStarProjection P)(h:A*P=P): P*A=P:= backJ p.isSelfAdjoint q.isSelfAdjoint q.isSelfAdjoint h
lemma climax (p:IsStarProjection A)(h:A*P=0)(q:IsStarProjection P): IsStarProjection (A+P):= ⟨show _*_=_ from by rw [mul_add,add_mul,add_mul,h,p.isIdempotentElem.eq,q.isIdempotentElem.eq,back p q h,zero_add,add_zero], p.isSelfAdjoint.add q.isSelfAdjoint⟩
lemma coin (p:IsStarProjection A)(K:Op I)(v:0<c)(ht:c≤1)(h:c • A≤K) : c • (1:Op I)≤K+(1-A):= calc
 _= c • A+c • (1-A):=by rw [←smul_add,add_sub_cancel]
 _ ≤ _:= add_le_add h ((smul_le_smul_of_nonneg_right ht p.one_sub.nonneg).trans_eq (one_smul ..))
lemma cheap_apply (p:IsStarProjection A)(v:Ket I): ‖acts A v‖≤‖v‖:=by
 apply (ContinuousLinearMap.le_opNorm ..).trans; rw [acts, Matrix.l2_opNorm_toEuclideanCLM]; apply le_trans (mul_le_mul_of_nonneg_right (p.norm_le _) (norm_nonneg _)); rw [one_mul]
structure Empties (P Q L:Op I): Prop where
 p : IsStarProjection P
 q : IsStarProjection Q
 l0 : L=1-(P+Q)
 orth : P*Q=0
structure Pass (P Q L A:Op I)(c:ℝ):Prop extends Empties P Q L where
 a : IsStarProjection A
 pos : 0<c
 small : c≤1
 payP : c • P≤P*A*P
 payQ : c • Q≤Q*(1-A)*Q
namespace Empties
variable (h:Empties P Q L)
include h
lemma r : IsStarProjection L := h.l0 ▸ (climax h.p h.orth h.q).one_sub -- avoid ▸ slow?
lemma PL : P*L=0:=by rw [h.l0,mul_sub,mul_add,mul_one,h.p.isIdempotentElem.eq,h.orth,add_zero,sub_self]
lemma LP : L*P=0:=back h.p h.r h.PL
lemma QP : Q*P=0:=back h.p h.q h.orth
lemma QL : Q*L=0:=by rw [h.l0,mul_sub,mul_add,mul_one,h.q.isIdempotentElem.eq,h.QP,zero_add,sub_self]
lemma LQ : L*Q=0:=back h.q h.r h.QL
lemma combo(v:Ket I): ‖acts P v‖^2+‖acts Q v‖^2+‖acts L v‖^2=‖v‖^2:=by rw [← Quad.e_proj h.p,← Quad.e_proj h.q,←Quad.e_proj h.r,← e_add,← e_add,h.l0, add_sub_cancel,e_one]
end Empties

-- upper estimate on punctures applies to any v in range R using Q holes.
lemma puncture (v:0<c)(u:c≤1)(p:IsStarProjection R)(q:IsStarProjection Q)(h:c • Q≤ Q*(1-R)*Q) : R*Q*R ≤ (1-c) • R:=by
 have ht : Q*R*Q≤(1-c) • Q:=by rw [mul_sub Q,mul_one,sub_mul,q.isIdempotentElem.eq] at h; rw [sub_smul,one_smul]; exact le_sub_comm.mp h -- tune
 let D:=R*Q; have he: star D*D=Q*R*Q:=by unfold D; rw [star_mul,p.isSelfAdjoint,q.isSelfAdjoint,←mul_assoc, mul_assoc Q R R,p.isIdempotentElem.eq]
 have hp: D*star D=R*Q*R:=by unfold D; rw [star_mul,p.isSelfAdjoint,q.isSelfAdjoint,←mul_assoc, mul_assoc R Q Q,q.isIdempotentElem.eq]
 let b:ℝ:=1-c; have hb:0≤b:=sub_nonneg.mpr u
 have hz : ‖D*star D‖≤b:=by
    rw [CStarRing.norm_self_mul_star, ←CStarRing.norm_star_mul_self]; apply (CStarAlgebra.norm_le_iff_le_algebraMap _ hb (star_mul_self_nonneg D)).mpr; rw [Algebra.algebraMap_eq_smul_one,he]; exact ht.trans (smul_le_smul_of_nonneg_left q.le_one hb)
 have hx := (op_le_norm_one (IsSelfAdjoint.mul_star_self D)).trans (smul_le_smul_of_nonneg_right hz zero_le_one); have hx:= s_mono p.isSelfAdjoint hx
 rwa [hp,←mul_assoc,←mul_assoc,p.isIdempotentElem.eq,mul_assoc (R*Q),p.isIdempotentElem.eq,Algebra.mul_smul_comm, Algebra.smul_mul_assoc,mul_one,p.isIdempotentElem.eq] at hx

def rent1 (P A:Op I):= Trans.beam P (A*P)
def rent0 (P A:Op I):= A-rent1 P A
namespace Pass
variable (h:Pass P Q L A c)
include h
lemma gate1 : Trans.Ready c P (A*P):=by
 refine ⟨h.p,by rw [mul_assoc,h.p.isIdempotentElem.eq],h.pos,?_⟩; unfold Trans.gram; rw [star_mul,h.p.isSelfAdjoint,h.a.isSelfAdjoint,←mul_assoc,mul_assoc P A A,h.a.isIdempotentElem.eq]; exact coin h.p _ h.pos h.small h.payP
lemma r1 : IsStarProjection (rent1 P A):=h.gate1.starP
lemma ray1: A*rent1 P A=rent1 P A:=by unfold rent1 Trans.beam; rw [←mul_assoc, ←mul_assoc,h.a.isIdempotentElem.eq]
lemma ray1': rent1 P A*A=rent1 P A:=across h.a h.r1 h.ray1
lemma riseP: rent1 P A*P=A*P:=by have ht:=h.gate1.continuousSpace; change rent1 P A*(A*P)=_ at ht; rwa [←mul_assoc,h.ray1'] at ht -- tune
lemma riseQ: P*rent1 P A=P*A:=by have ht:= congrArg star h.riseP; rwa [star_mul,star_mul,h.r1.isSelfAdjoint,h.p.isSelfAdjoint,h.a.isSelfAdjoint] at ht
lemma r0 : IsStarProjection (rent0 P A) := (h.r1.le_iff_sub h.a).mp ((h.r1.le_iff_mul_eq_right h.a).mpr h.ray1)
lemma ray0: A*rent0 P A=rent0 P A:=by unfold rent0; rw [mul_sub,h.ray1,h.a.isIdempotentElem.eq]
lemma ray0': rent0 P A*A=rent0 P A:=across h.a h.r0 h.ray0
lemma sap: rent1 P A*rent0 P A=0:=by rw [rent0,mul_sub,h.ray1',h.r1.isIdempotentElem.eq,sub_self]
lemma sap' : rent0 P A*rent1 P A=0:=back h.r1 h.r0 h.sap
lemma cold: P* rent0 P A=0:=by rw [rent0,mul_sub, h.riseQ, sub_self]
lemma stay(v:Ket I) (p:acts A v=v)(q:acts P v=0): acts (rent0 P A) v=v:=by
 let X:= Trans.gram P (A*P); have he: acts (star (A*P)) v=0:=by rw [star_mul,h.a.isSelfAdjoint,h.p.isSelfAdjoint, act_mul,p,q]
 unfold rent0; rw [act_sub,p, rent1,Trans.beam,Trans.pinv,act_mul,act_mul,act_mul, he,map_zero,map_zero,map_zero,sub_zero]
lemma pay0 : c • Q≤ Q*(1-rent0 P A)*Q:=h.payQ.trans (s_mono h.q.isSelfAdjoint (sub_le_sub_left ((h.r0.le_iff_mul_eq_right h.a).mpr h.ray0) _))
lemma l_est : let X:= L*rent0 P A; c • (rent0 P A) ≤ star X * X := by
 intro X; let E:= rent0 P A; have ht:= puncture h.pos h.small h.r0 h.q h.pay0
 have hp: star X*X=E-E*Q*E:=by
    unfold X; rw [star_mul,h.toEmpties.r.isSelfAdjoint,h.r0.isSelfAdjoint,←mul_assoc,mul_assoc E,h.toEmpties.r.isIdempotentElem.eq,h.toEmpties.l0,mul_sub,mul_one,sub_mul,mul_add,add_mul,h.r0.isIdempotentElem.eq, mul_assoc E P E,h.cold,mul_zero,zero_add] -- tune pattern E
 rw [hp]; apply le_sub_comm.mpr; rw [sub_smul,one_smul] at ht; exact ht
lemma gate0 : Trans.Ready c (rent0 P A) (L* rent0 P A):= ⟨h.r0,by rw [mul_assoc,h.r0.isIdempotentElem.eq], h.pos, coin h.r0 _ h.pos h.small h.l_est⟩
lemma vis_cap (v:Ket I)(p:acts (rent0 P A) v=v): c*‖v‖≤‖acts L v‖:=by
 have ht:= e_mono h.l_est v; rw [e_pow,e_scale,e_proj h.r0,act_mul,p] at ht
 apply (sq_le_sq₀ (mul_nonneg h.pos.le (norm_nonneg _)) (norm_nonneg _)).mp; rw [mul_pow]; exact (mul_le_mul_of_nonneg_right (by nlinarith only [h.pos,h.small] : c^2 ≤ c) (sq_nonneg _)).trans ht
lemma esc1 (v:Ket I)(t: acts (rent1 P A) v=v) : c*‖v‖≤‖acts P v‖:=by
 have ht: acts A v=v:=by nth_rw 1 [←t]; rw [←act_mul,h.ray1,t]
 let D:=Trans.pinv P (A*P); let B:=(Trans.gram P (A*P))⁻¹; have he: acts D v=acts B (acts P v):=by unfold D Trans.pinv; rw [act_mul,star_mul,h.p.isSelfAdjoint,h.a.isSelfAdjoint,act_mul,ht]
 have hp: ‖acts D v‖ ≤ c⁻¹*‖acts P v‖:=by rw [he]; apply (ContinuousLinearMap.le_opNorm ..).trans; rw [acts,Matrix.l2_opNorm_toEuclideanCLM]; exact mul_le_mul_of_nonneg_right h.gate1.boundG (norm_nonneg _)
 have hz:‖v‖≤c⁻¹* ‖acts P v‖:=by nth_rw 1 [← t]; rw [rent1,Trans.beam,act_mul,act_mul]; exact (cheap_apply h.a _).trans ((cheap_apply h.p _).trans hp)
 exact (mul_le_mul_of_nonneg_left hz h.pos.le).trans_eq (by rw [←mul_assoc,mul_inv_cancel₀ h.pos.ne',one_mul])
lemma opens : let S:=star (Trans.pinv P (A*P)); P*rent1 P A*S=P := by
 intro S; have hp:=congrArg star h.gate1.paid; rw [star_mul,star_mul,h.p.isSelfAdjoint,h.a.isSelfAdjoint] at hp; rwa [h.riseQ]
end Pass
end Cellar
end YM.CF.BPress.Spin

import YM.CF.Kea.Cool
import Mathlib.Analysis.Matrix.PosDef
set_option autoImplicit false
noncomputable section
namespace YM.CF.Flare
open Function Filter Finset NormedSpace Lattice Laurent Kea Lat BZ Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {n:Type*}[Fintype n][DecidableEq n]{P Q W V N Y K: Op n} {a:ℝ}
lemma inch (h:IsStarProjection P)(hp:Matrix.trace P=0):P=0:= ((Matrix.nonneg_iff_posSemidef.mp h.nonneg).trace_eq_zero_iff).mp hp
lemma volta(h:IsStarProjection P)(p:IsStarProjection Q)(q:Q.trace=P.trace)(u:star V*W=1)(v:P*K=K)(k:K*(Q*W*P)=star (K*(Q*W*P)))(t:K*Q=K)(e: Q*W*P*K=Q): Clad P Q W V K:=by
 let L:= Q*W*P; have hp:L*P=L:=by unfold L; rw [mul_assoc,h.1]
 have he:(P-K*L)*(P-K*L)=(P-K*L):=by
   have hv:K * L*K=K:=by rw [mul_assoc,e,t]
   rw [mul_sub,sub_mul,h.isIdempotentElem.eq, mul_assoc K L P,hp, sub_mul,←mul_assoc P K, v, ←mul_assoc _ K, hv,sub_self, sub_zero] -- tune
 have hh:IsSelfAdjoint (P-K*L):=by rw [isSelfAdjoint_iff,star_sub,h.2,k.symm]
 have hx: Matrix.trace (P-K*L)=0:=by rw [Matrix.trace_sub, Matrix.trace_mul_comm,e,q,sub_self]
 exact ⟨h,p,u,(sub_eq_zero.mp (inch ⟨he,hh⟩ hx)).symm,e,v,t⟩
lemma bridge (h:IsStarProjection P)(p:IsStarProjection Q)(q:Q.trace=P.trace)(u:star V*W=1)(t:0<a)(z:N=a⁻¹ • (Q*W*P))(e:(N*star N+(1-Q))*Y=1):Clad P Q W V (a⁻¹ • (star N * Y * Q)):=by
 let F:=(N*star N+(1-Q)); let S:=star N*Y*Q; let K:= a⁻¹ • S; let X:=Q*W*P
 have hy: X=a • N:=by rw [z]; exact (smul_inv_smul₀ t.ne' _).symm
 have hg:Q*N=N:=by rw [z,Matrix.mul_smul,←mul_assoc,←mul_assoc,p.1]
 have hv:P* star N=star N:=by nth_rw 1 [←h.2]; rw [← star_mul,z,Matrix.smul_mul,mul_assoc,h.1]
 have he:star F=F:=by simp only [F,star_add,star_mul,star_star,star_sub,star_one,p.isSelfAdjoint.star_eq]
 have hx:Y*F=1:=mul_eq_one_comm.mp e; have hh:=congrArg star hx; rw [star_mul, star_one,he] at hh; have ha:Y=star Y:=by nth_rw 1 [←mul_one Y,←hh]; rw [←mul_assoc,hx,one_mul]
 have hQ:Q*F=N*star N:=by unfold F; rw [mul_add,←mul_assoc,hg,mul_sub,mul_one,p.1,sub_self,add_zero]
 have ht: X*K=Q:=by rw [hy]; unfold K S; rw [Matrix.smul_mul,Matrix.mul_smul,smul_inv_smul₀ t.ne',←mul_assoc,←mul_assoc,←hQ,mul_assoc _ F,e,mul_one,p.1]
 refine volta h p q u ?_ ?_ ?_ ht
 · rw [Matrix.mul_smul,← mul_assoc,← mul_assoc,hv]
 · change K*X=star (K*X); rw [hy]; unfold K S; rw [Matrix.smul_mul,Matrix.mul_smul, inv_smul_smul₀ t.ne',mul_assoc _ Q,hg,star_mul,star_mul, star_star, ←ha,mul_assoc]
 rw [Matrix.smul_mul,mul_assoc,p.1]
lemma port_inv [Nonempty n] (A:Op n)(h:‖A-1‖≤1/2):∃ B:Op n,A*B=1∧ ‖B‖≤2:=by
 obtain ⟨U,g⟩:= nearOne ((norm_sub_rev ..).trans_le h|>.trans_lt (by norm_num)); let B:Op n:=↑(U⁻¹); have he:A*B=1:=by rw [←g]; simp [B]
 refine ⟨B,he,?_⟩; have hx: ‖B-1‖ ≤ (1/2)*‖B‖:=by
   apply le_trans _ (mul_le_mul_of_nonneg_right h (norm_nonneg B)); rw [norm_sub_rev,  show 1-B=(A-1)*B by rw [sub_mul,one_mul,he]]; exact norm_mul_le ..
 have hg:=norm_le_norm_sub_add B 1; rw [norm_one] at hg; linarith
end YM.CF.Flare

import YM.CF.BPress.Pf.Arrival
import YM.CF.BPress.Pf.Abid
/-! Outer Wick spaces tailored to this model. Gap grammar. Explicit complement of dual ramp. The price of the resulting oblique pair is a row price on each of four matrix channels.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Pf
open Function Filter NormedSpace Finset Fock Spin Spin.Quad Spin.Cellar Spin.Cellar.Pass
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I][Nonempty I]{P Q A T L C D:Op I}{c d r ε:ℝ}
-- anti-C cov where needed, real projections
structure PairBoard (P Q L C:Op I) : Prop extends Empties P Q L where
    p_real: cc P=P
    q_real: cc Q=Q
    pC:P*C=C*P
    qC:Q*C=C*Q

lemma cc_nn (p:0≤A):0≤ cc A:=by obtain ⟨U,h⟩:= CStarAlgebra.nonneg_iff_eq_star_mul_self.mp p; rw [h,cc_mul,cc_star]; exact star_mul_self_nonneg _
lemma cc_le (p:A≤P): cc A ≤ cc P:= sub_nonneg.mp (by rw [← cc_sub]; exact cc_nn (sub_nonneg.mpr p))
lemma rank_tr (A:Op I)(p:IsStarProjection A): (cc A).trace=A.trace:=by rw [cc,p.isSelfAdjoint]; simp
lemma match_proj (u:IsStarProjection P)(h:IsStarProjection Q)(p: P≤Q)(q:P.trace= Q.trace): P=Q:=by
 obtain ⟨U,s,H⟩:=spot_projection _ ((u.le_iff_sub h).mp p); have ht: (Q-P).trace=0:=by rw [Matrix.trace_sub,q,sub_self]
 rw [H,trace_twist,trace_cut] at ht; rw [show s=∅ from (card_eq_zero.mp (by exact_mod_cast ht)), show cutM (∅:Finset I)=0 from (by unfold cutM; simp),map_zero] at H; exact (sub_eq_zero.mp H).symm

namespace Dual
variable (K: PairBoard P Q L C)
include K
lemma L_real:cc L=L:=by rw [K.l0]; simp only [cc_sub,cc_one,cc_add,K.p_real,K.q_real]
lemma LC:L*C=C*L:=by rw [K.l0]; simp only [sub_mul,mul_sub,one_mul,mul_one,add_mul,mul_add,K.pC,K.qC]
lemma dualPass (X:Pass P Q L A c) : Pass Q P L (1-cc A) c :=by
 have ht:= cc_le X.payQ; rw [cc_rsmul,K.q_real,cc_mul,K.q_real,cc_mul,K.q_real,cc_sub,cc_one] at ht -- tune
 refine ⟨⟨K.q,K.p,by rw [K.l0,add_comm P], X.toEmpties.QP⟩, (ccProj X.a).one_sub,X.pos,X.small,ht,?_⟩
 have hv:= cc_le X.payP; rw [cc_rsmul,K.p_real,cc_mul,K.p_real,cc_mul,K.p_real] at hv; rw [sub_sub_cancel]; exact hv
lemma rampO (X:Pass P Q L A c): ramp L Q (1-cc A)= L-cc (ramp L P A):=by
 let K':=K; let V:=rent0 P A; let S:=cc V; let W:=1-cc A; let D:=rent0 Q W; let T:=ramp L Q W; let N:=ramp L P A; let R:=cc N
 have Y:= dualPass K X; have hr:IsStarProjection S:= ccProj X.r0; have hR:IsStarProjection R:=ccProj X.ramp_star
 have hm: L*R=R:= by have ht:= congrArg cc X.ramp_L; rwa [cc_mul,L_real K] at ht
 have hs: S*D=0:=by
    have he: S*cc A=S:=by rw [←cc_mul,X.ray0'] -- tune
    have hg: (1-cc A)*D=D:=Y.ray0; nth_rw 1 [← hg,← he]; rw [←mul_assoc, mul_assoc S, (ccProj X.a).mul_one_sub_self,mul_zero,zero_mul]
 have hy: S*L*D=0:=by
    have he:S*P=0:=by rw [← K.p_real,←cc_mul,back K.p X.r0 X.cold,cc_zero];
    have hk:Q*D=0:=Y.cold
    rw [K.l0,mul_sub,mul_one,sub_mul,hs,mul_add,he,zero_add,mul_assoc,hk]; simp
 have hx: R*T=0:=by
    let V':=cc (Trans.pinv V (L*V)); have hu:T=L*D * (Trans.pinv D (L*D)):=rfl
    have hg: R=star V'*S* L:=by
       nth_rw 1 [← hR.isSelfAdjoint]; apply Eq.trans (congrArg star (show R=L*S*V' from (by unfold R N ramp Trans.beam; rw [cc_mul,cc_mul,L_real K]))); rw [star_mul,star_mul,K.toEmpties.r.isSelfAdjoint,hr.isSelfAdjoint,mul_assoc]
    rw [hg,hu]; simp only [←mul_assoc]; rw [mul_assoc (star V'*S) L, K.toEmpties.r.isIdempotentElem.eq,show star V' * S*L*D=0 from (by rw [mul_assoc (star V') S L, mul_assoc (star V'),hy,mul_zero]),zero_mul]

 have hC: IsStarProjection (R+T):=climax hR hx Y.ramp_star; have he:(R+T).trace=L.trace:=by
    have ht:N.trace=V.trace:=X.gate0.trace; have hm:T.trace=D.trace:=Y.gate0.trace; rw [Matrix.trace_add, show R.trace=N.trace from rank_tr _ X.ramp_star,ht,hm]; unfold D V rent0; rw [Matrix.trace_sub,Matrix.trace_sub, show (rent1 Q W).trace=Q.trace from Y.gate1.trace, show (rent1 P A).trace=P.trace from X.gate1.trace]; unfold W; rw [Matrix.trace_sub,K.l0,Matrix.trace_sub,Matrix.trace_add,rank_tr A X.a]; abel
 have hp:(R+T)=L:=match_proj hC K.toEmpties.r ((hC.le_iff_mul_eq_right K.toEmpties.r).mpr (by rw [mul_add,hm,Y.ramp_L])) he; change T=L-R; rw [←hp,add_sub_cancel_left]
lemma toll_exit (X:Pass P Q L A c): toll (P+ramp L P A) C=toll (ramp L P A) C:=by
 let R:= ramp L P A; have hp:= X.ramp_P; have hm:=back K.p X.ramp_star hp; have ht:L*cc R=cc R:=by rw [← L_real K, ← cc_mul,X.ramp_L]
 unfold toll; rw [cc_add,K.p_real];
 have hh:C*P=P*C:=K.pC.symm; have hu:(1-(P+R))*P=0:=by simp only [sub_mul,one_mul,add_mul,show R*P=0 from hm,K.p.isIdempotentElem.eq, sub_self,add_zero]
 have hy:P*C*cc R=0:=by rw [K.pC,mul_assoc, ← ht, ←mul_assoc P,K.toEmpties.PL,zero_mul,mul_zero]
 rw [mul_add, mul_assoc (1-_), hh, ←mul_assoc (1-_) P,hu,zero_mul,zero_add]; change (1-(P+R))*C*_= _; rw [add_comm P,←sub_sub,sub_mul,sub_mul _ (P*C),hy,sub_zero]
lemma lost_exit (X:Pass P Q L A c)(g: Bore (P+ramp L P A) C ε): lost (P+ramp L P A) C=lost (ramp L P A) C:=by
 let R:=ramp L P A; let T:=P+R; have he (A: Op I)(h:IsStarProjection A):A*C*(1-cc A)= -(toll A C)ᵀ:= by
    unfold toll; rw [Matrix.transpose_mul, Matrix.transpose_mul,ccT,h.isSelfAdjoint,g.sk,Matrix.transpose_sub,Matrix.transpose_one, show Aᵀ=cc A by rw [cc,h.isSelfAdjoint], neg_mul,mul_neg,neg_neg,mul_assoc]
 have hf:Bore R C ε:=⟨X.ramp_star,g.unit,g.sk,toll_exit K X ▸ g.low,g.hi⟩
 rw [g.portion,he (P+R) g.p,toll_exit K X,hf.portion,he _ X.ramp_star] -- tune
end Dual
end YM.CF.BPress.Pf

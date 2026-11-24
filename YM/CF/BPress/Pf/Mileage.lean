import YM.CF.BPress.Pf.Arrival
import Mathlib.LinearAlgebra.Matrix.SchurComplement
/-! real norm determinants: eq:B-plogre, ready to use even if empty patch. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Pf
open Function Filter NormedSpace Finset Fock Spin Spin.Quad Spin.Cellar Spin.Cellar.Pass
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
namespace Mileage
variable {I : Type}[Fintype I][LinearOrder I][Nonempty I]{P Q L A:Op I}{c:ℝ}
lemma ride_switch (p:IsStarProjection P)(q:IsStarProjection Q)(h:P.trace=Q.trace) : (terrace P Q).det=(terrace Q P).det:=by
 let α (P T: Op I)(t:ℝ):= terrace P T+t • P; obtain ⟨U,S,hx⟩:=spot_projection Q q; have he:Q.trace=(S.card:ℂ):=by rw [hx,trace_twist,trace_cut]
 have hm (P Q:Op I)(p:IsStarProjection P)(q:IsStarProjection Q)(h:P.trace=(S.card:ℂ))(x:ℝ)(s:0<x): (α P Q x).det=(x:ℂ)^S.card*(1+ (x⁻¹ • (P*Q)) * (Q*P)).det:=by
    have hg:(x⁻¹ • (P*Q))*(Q*P)=x⁻¹ • (P*Q*P):=by rw [Algebra.smul_mul_assoc,←mul_assoc,mul_assoc P,q.isIdempotentElem.eq]; -- tune
    rw [hg,← Arrival.det_scale _ p h, ←Matrix.det_mul]; congr 1
    let E:= P*Q*P; let K:=1-P; change E+K+x • P=(1+(x-1) • P)*(1+x⁻¹ • E); rw [show 1+(x-1) • P= K+x • P from by unfold K; module, mul_add,mul_one,add_mul K,Algebra.mul_smul_comm, show K*E=0 from by unfold K E; rw [←mul_assoc, ←mul_assoc,p.one_sub_mul_self,zero_mul,zero_mul], Algebra.smul_mul_assoc,Algebra.mul_smul_comm,show P*E=E from by unfold E; rw [←mul_assoc,←mul_assoc,p.isIdempotentElem.eq],smul_smul,mul_inv_cancel₀ s.ne',smul_zero,one_smul]; abel
 have ha(P Q:Op I):Continuous (fun t=> (α P Q t).det):= Continuous.matrix_det (by unfold α; fun_prop)
 have ht: (α P Q 0).det= (α Q P 0).det:= by
    apply tendsto_nhds_unique ((ha P Q).continuousWithinAt (s:=Set.Ioi (0:ℝ))).tendsto; refine Tendsto.congr' (f₁:=fun x=> (α Q P x).det) ?_ (ha Q P).continuousWithinAt.tendsto; filter_upwards [self_mem_nhdsWithin] with i hi; change (α Q P i).det=(α P Q i).det; rw [hm _ _ p q (h.trans he) i hi, hm _ _ q p he i hi, Matrix.det_one_add_mul_comm (i⁻¹ • (Q*P)),Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
 simpa only [α,zero_smul,add_zero] using ht
lemma cellar (h:Pass P Q L A c) : let S:= slide P Q L A 0; (Trans.gram A S).det= (terrace P A).det*(terrace Q (1-rent0 P A)).det:=by
 intro S; let V:=rent1 P A; let W:=rent0 P A; let X:=V*(1-P)*V; let Y:= W*Q*W; let U:= h.toEmpties
 have hx: V*V=V:= h.r1.isIdempotentElem.eq; have hw:W*W=W:=h.r0.isIdempotentElem.eq
 have hz:1-X= terrace V P:=by unfold terrace X; rw [mul_sub,mul_one,sub_mul,hx]; abel
 have hp: terrace P V=terrace P A:=by unfold terrace; rw [h.riseQ]
 have ht:1-Q*W*Q=terrace Q (1-W):=by unfold terrace; rw [mul_sub,mul_one,sub_mul,h.q.isIdempotentElem.eq]; abel
 have H₁:(terrace P A).det=(1-X).det:=by rw [hz,←hp,ride_switch h.p h.r1 h.gate1.trace.symm]
 have H₂:(1-Y).det=(terrace Q (1-W)).det:=by rw [←ht, show Y=(W*Q)*(Q*W) from ?_, Matrix.det_one_sub_mul_comm, ←mul_assoc,mul_assoc Q, hw]; unfold Y; rw [←mul_assoc, mul_assoc W Q Q,h.q.isIdempotentElem.eq]
 change (Trans.gram A S).det= (terrace _ _).det*(terrace Q (1-W)).det; rw [H₁,← H₂,← Matrix.det_mul]; congr 1
 have hV:W*L*W=W-Y:=by rw [h.l0,mul_sub,mul_one,sub_mul,hw,mul_add,add_mul, mul_assoc W P W, h.cold]; simp only [mul_zero,zero_add]; rfl; -- tune
 have hy: X*Y=0:=by unfold X Y; rw [← mul_assoc, ←mul_assoc _ W, mul_assoc _ V W,h.sap, mul_zero,zero_mul,zero_mul]
 unfold Trans.gram; rw [show S=P*V+L*W from h.floor_S,star_add,star_mul,star_mul,h.p.isSelfAdjoint.star_eq, h.r1.isSelfAdjoint, h.r0.isSelfAdjoint,U.r.isSelfAdjoint]; change (V*P+W*L)*_+_= _; rw [mul_add,add_mul,add_mul (V*P),mul_sub (1-X),mul_one, sub_mul 1 X,hy,one_mul,sub_zero]
 have hb: W*L*(P*V)=0:=by rw [←mul_assoc,mul_assoc W,U.LP,mul_zero,zero_mul]
 have ha: V*P*(L*W)=0:=by rw [← mul_assoc, mul_assoc V,U.PL,mul_zero,zero_mul]
 rw [hb,ha, ←mul_assoc (V*P),mul_assoc V P P,h.p.isIdempotentElem.eq,←mul_assoc (W*L),mul_assoc W L L, U.r.isIdempotentElem.eq,hV]
 unfold X; rw [mul_sub,mul_one,sub_mul,hx]; rw [show A=V+W from by unfold V W rent0; abel]; abel
end Mileage
end YM.CF.BPress.Pf

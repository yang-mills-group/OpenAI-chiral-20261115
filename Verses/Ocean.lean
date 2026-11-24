import YM.SU5.Relativistic.Schist
import YM.SU5.Relativistic.Raspa
import Verses.Database
/-! # pinpoint charge. On clean ORBIT. (For unrepaired dirty count by t.) -/
set_option autoImplicit false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.CF.Papyrus.Franc
open Function Filter NormedSpace Metric Fock Finset Lattice Lat Fir Ember Thera BPress.Spin.Blank Rush SU Scroll Tulip Dial Cube Skye Pannier Pannier.Chancel Buffered Pastry
open Crest.Sleet Pannier.Damask
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra

open CF.Window Matrix Papyrus.Granat Thera
namespace Verses
variable {I:Type}[LinearOrder I][Fintype I]{C:ℝ}
private lemma sat (V:Op I) (p:0≤V): ‖V.det‖ ≤ Real.exp ((V-1).trace.re):=by
 obtain ⟨U,d,e⟩:= spectral_exists V (IsSelfAdjoint.of_nonneg p); subst V; rw [←spectral_zero U,spectral_le] at p
 rw [← spectral_one U,spectral_sub,spectral,spectral,det_twist,trace_twist,Matrix.trace_diagonal, Matrix.det_diagonal,norm_prod]; push_cast -- tune
 have he(i:I): ‖(↑(d i):ℂ)‖ ≤ Real.exp (d i-1):=by have hx:= Real.add_one_le_exp (d i-1); rw [Complex.norm_real, Real.norm_of_nonneg (p i)]; linarith
 rw [show ( (∑ i:I, (↑((d-1) i):ℂ):ℂ)).re= (∑ i:I, (d i-1)) from (?_), Real.exp_sum]
 · exact prod_le_prod (fun i _=> norm_nonneg _) (fun i _=>he i)
 rw [←Complex.ofReal_sum,Complex.ofReal_re]; rfl
-- appetite bound.I 
lemma appetite (V P:Op I) (p:IsStarProjection V)(f:Wave I)(h:Sea V f): ‖acts (quant P) f‖ ≤ Real.exp (((star P*P-1)*V).trace.re/2):=by
 let K:=star P*P; let O:=V*K*V+(1-V)
 have hv:0≤ V*K*V:=le_trans (star_mul_self_nonneg (P*V)) (le_of_eq (by rw [star_mul,p.isSelfAdjoint]; unfold K; noncomm_ring))
 have hp:0≤O:=add_nonneg hv p.one_sub.nonneg -- method
 let F:= acts (quant P) f; have ht:inner ℂ F F=O.det:=by
    have hf := meadow p f h K
    rw [←hf]; change inner ℂ (acts (quant P) f) F=inner ℂ f (acts (quant (star P*P)) f); rw [quant_mul,quant_star,act_mul]; exact (by nth_rw 1 [←star_star (quant P)]; rw [act_inner])
 rw [inner_self_eq_norm_sq_to_K] at ht
 apply le_of_pow_le_pow_left₀ (n:=2) (by norm_num) (Real.exp_pos _).le
 change ‖F‖^2≤ Real.exp (((K-1)*V).trace.re/2)^2
 rw [pow_two (Real.exp _),←Real.exp_add,add_halves]
 refine le_trans (le_of_eq (show ‖F‖^2=‖O.det‖ by rw [←ht,norm_pow,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _)])) ((sat _ hp).trans_eq (congrArg (fun x:ℂ=>Real.exp x.re) ?_))
 unfold O; rw [show V*K*V+(1-V)-1= V*K*V -V by abel, Matrix.trace_sub,mul_assoc V,Matrix.trace_mul_comm V,mul_assoc K,p.isIdempotentElem.eq,sub_mul,Matrix.trace_sub,one_mul]
lemma entry_dot (A B:Op I)(C:ℝ)(h:∀ i:I,∀ j:I, ‖A i j‖ ≤ C) : ((A*B).trace).re ≤ C*entryBudget B:=by
 apply le_trans (Complex.re_le_norm _)
 unfold Matrix.trace Matrix.diag; simp_rw [Matrix.mul_apply]; unfold entryBudget; rw [sum_comm]; rw [Finset.mul_sum]
 apply (norm_sum_le ..).trans; apply sum_le_sum; intro i _; rw [Finset.mul_sum]; apply (norm_sum_le ..).trans; apply sum_le_sum; intro j _; rw [norm_mul]; gcongr; exact h j i
lemma attacking (T:Shaft I)(P:Op I)(p:IsStarProjection P)(ht:T.sell*P=P)(hp:fiber T C)(hC:0≤C) (A:Op I)(k:IsStarProjection A)(v:Wave I)(hv:Sea A v): ‖acts (quant T.sell) v‖ ≤ Real.exp ((C*C+1)*entryBudget (A-P)/2):=by
 apply (appetite A T.sell k v hv).trans (Real.exp_le_exp.mpr _)
 apply div_le_div_of_nonneg_right _ (by positivity)
 let S:=T.sell; let V:=star S*S-1
 have ha: V*P= star S*P-P:=by unfold V; rw [sub_mul,mul_assoc,ht,one_mul]
 have hg:P*star S=P:= by rw [← (show star P=P from p.isSelfAdjoint)]; nth_rw 1 [←star_mul]; rw [ht]
 have h':(V*P).trace=0:=by rw [ha,Matrix.trace_sub,Matrix.trace_mul_comm,hg,sub_self]
 rw [show A=A-P+P from (sub_add_cancel ..).symm] -- all A occurrences rewrites rhs entryBudget; use add etc
 change (V*(A-P+P)).trace.re≤ _
 rw [mul_add,Matrix.trace_add,h',add_zero,add_sub_cancel_right (A-P)]
 apply entry_dot
 intro i j; unfold V; simp only [Matrix.sub_apply]; refine (norm_sub_le ..).trans (add_le_add ?_ ?_)
 · have he:(star S*S) i j=inner ℂ (acts S (basisKet i)) (acts S (basisKet j)):=by rw [←basis_act (star S*S) _ _,←basis_inner,act_mul,←act_inner,star_star] -- check parameters
   rw [he]; exact (norm_inner_le_norm ..).trans (mul_le_mul (hp.fst _) (hp.fst _) (norm_nonneg _) hC)
 rw [Matrix.one_apply]; split <;> simp
end Verses
end YM.CF.Papyrus.Franc

import YM.SU5.Relativistic.Sable
import YM.CF.BProof.Align.Pastel
/-! # crater Lipschitz cent costs with restricted ROW norm. Summing powers in full norm loses volume bracket. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.CF.Papyrus.Granat
open Function Filter Finset Fock Branch MeasureTheory NormedSpace
open BProof.Align
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I][Nonempty I] {a ε r b C:ℝ} {P Q U R:Op I}{S: Finset I}
private lemma trim (A:Op I)(h:‖(P-Q)*cutM S‖≤ε) (t:‖P-Q‖≤r)(c:0 ≤ ε): ‖Matrix.trace (A*(P-Q))‖ ≤ ‖A‖*(Fintype.card I*ε+ Sᶜ.card*r):=by
 let X:=A*(P-Q); let f(i:I):=‖X i i‖; change ‖X.trace‖≤_
 have hx(i:I):f i≤ ‖A‖ *ε+ if i∈ Sᶜ then ‖A‖*r else 0:=by
    split_ifs with p; · apply le_trans (le_trans (norm_entry X i i) ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_left t (norm_nonneg _)))) (le_add_of_nonneg_left (mul_nonneg (norm_nonneg _) c))
    unfold f; rw [show X i i=(X*cutM S) i i from ?_]; swap; · rw [cutM,Matrix.mul_diagonal,if_pos (notMem_compl.mp p), mul_one]
    apply (norm_entry _ _ _).trans; rw [add_zero]; unfold X; rw [mul_assoc]; exact (norm_mul_le ..).trans (mul_le_mul_of_nonneg_left h (norm_nonneg _))
 apply (norm_sum_le ..).trans; apply (sum_le_sum (fun i _=> hx i)).trans; rw [sum_add_distrib,sum_ite]; simp only [sum_const,sum_const_zero,card_univ,nsmul_eq_mul,add_zero,filter_mem_eq_inter,univ_inter]; exact le_of_eq (by ring) -- tune
private lemma terms (h:∀ A:Op I, ‖Matrix.trace (A*(P-Q))‖ ≤ ‖A‖*C) (t:0≤C)(p:‖P‖≤r)(q:‖Q‖≤r)(i:ℕ)(A:Op I) :
    ‖Matrix.trace (A*(P^(i+1)-Q^(i+1)))‖ ≤ (i+1:ℝ)*r^i * ‖A‖ * C:=by -- ring
 have hr:0≤r:=(norm_nonneg _).trans p
 induction i generalizing A with
 | zero=> simpa using h A
 | succ i ih =>
    let W:= A*P; let D:=Q^(i+1); let X:=P^(i+1)
    rw [pow_succ' P (i+1),pow_succ' Q (i+1),show A*(P*X-Q*D) = W*(X-D) + (A*(P-Q))*D by unfold W; noncomm_ring, Matrix.trace_add,Matrix.trace_mul_comm (A*(P-Q)),←mul_assoc]
    apply (norm_add_le ..).trans; apply le_trans (add_le_add (ih W) (h _))
    have hW:‖W‖≤ ‖A‖*r:= (norm_mul_le ..).trans (mul_le_mul_of_nonneg_left p (norm_nonneg _))
    have hD:‖D*A‖ ≤ r^(i+1)*‖A‖:= (norm_mul_le ..).trans (mul_le_mul_of_nonneg_right ((norm_pow_le ..).trans (pow_le_pow_left₀ (norm_nonneg _) q _)) (norm_nonneg _))
    apply (add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW (by positivity)) t) (mul_le_mul_of_nonneg_right hD t)).trans_eq; rw [pow_succ]; push_cast; ring
lemma prose (h:∀ A:Op I, ‖Matrix.trace (A*(P-Q))‖ ≤ ‖A‖*C) (t:0≤C)(p:‖P‖≤r)(q:‖Q‖≤r)(e:r<1) :
    Real.log ‖(1+P).det‖≤ Real.log ‖(1+Q).det‖+ C/(1-r):=by
 let X(P:Op I)(i:ℕ) := bcoef i • P^(i+1)
 have he(A:Op I)(u:‖A‖≤r): HasSum (fun i:ℕ=> ((X A i).trace).re) (Real.log ‖(1+A).det‖):=by
    rw [BProof.Align.logNorm (u.trans_lt e)]; let f:= (Matrix.traceLinearMap I ℝ ℂ).toContinuousLinearMap; exact HasSum.mapL Complex.reCLM (HasSum.mapL f ((sumPast (u.trans_lt e)).hasSum)) -- tune matrix
 have hr:0≤r:=(norm_nonneg _).trans p
 refine hasSum_le (fun i=>?_ ) (he P p) ((he Q q).add (show HasSum (fun i:ℕ=> C * r^i) (C/(1-r)) from ?_)); swap
 · rw [div_eq_mul_inv]; exact (hasSum_geometric_of_lt_one hr e).mul_left C
 have hv : ‖(X P i-X Q i).trace‖ ≤ C * r^i:=by
    unfold X; rw [←smul_sub,Matrix.trace_smul,norm_smul,biCoeff,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,norm_inv,Real.norm_of_nonneg (by positivity)]
    have hx : ((1:Op I)*(P^(i+1)-Q^(i+1)))=(P^(i+1)-Q^(i+1)):=one_mul _; have hg:= terms h t p q i 1; rw [hx,norm_one,mul_one] at hg; refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans_eq ?_; field_simp
 have hu:= (le_abs_self (Complex.re (X P i-X Q i).trace)).trans (Complex.abs_re_le_norm ..); have hm:= hu.trans hv; rw [Matrix.trace_sub, Complex.sub_re] at hm; linarith
private lemma which (h:IsStarProjection U) : Bolt U P a-1= -(1-a^2) • (U*(1-P)*U):=by
 unfold Bolt; rw [mul_add,add_mul,Algebra.mul_smul_comm,Algebra.smul_mul_assoc, neg_smul,sub_smul,one_smul]; let A:=U*(1-P)*U
 have he:U*P*U=U-A:=by unfold A; rw [mul_sub,mul_one,sub_mul,h.isIdempotentElem.eq]; abel
 rw [he]; unfold A; abel
private lemma span_leg (g:IsStarProjection P)(h:IsStarProjection U) (p:0<a)(t:a≤1):‖Bolt U P a-1‖ ≤ 1-a^2:=by
 have hx:0 ≤ 1-a^2:= sub_nonneg.mpr (pow_le_one₀ p.le t)
 rw [which h,norm_smul,norm_neg,Real.norm_of_nonneg hx]; refine mul_le_of_le_one_right hx ?_; exact (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (h.norm_le _)).trans ((norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (h.norm_le _)).trans (g.one_sub.norm_le _))))
private lemma span_diag (p:IsStarProjection U)(q:IsStarProjection P):
    ‖(Bolt U P a).det‖= (Bolt U P a).det.re:=by
 have hs:0≤ P+(a^2:ℝ) • (1-P) := add_nonneg q.nonneg (smul_nonneg (sq_nonneg _) q.one_sub.nonneg)
 obtain ⟨F,hf⟩:= CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hs
 have hk: 0 ≤ Bolt U P a:= add_nonneg (b:=1-U) (by
    refine le_trans (star_mul_self_nonneg (F*U)) (le_of_eq ?_); rw [star_mul,p.isSelfAdjoint,hf]; noncomm_ring) p.one_sub.nonneg
 have h:0≤(Bolt U P a).det:=(Matrix.nonneg_iff_posSemidef.mp hk).det_nonneg
 have ht:= h.1; have hu:= h.2; let L:= (Bolt U P a).det; let d:=L.re
 have hx:L=(d:ℂ):=Complex.ext rfl (by simp only [Complex.ofReal_im]; exact hu.symm)
 change ‖L‖=d; rw [hx,Complex.norm_real,Real.norm_of_nonneg (show 0≤d from ht)]
lemma hopeful (p:IsStarProjection U)(q:IsStarProjection P)(h:IsStarProjection Q)(e:0<a) (t:a≤1) (v:U*cutM S=cutM S*U) (c:0≤ε)(f:‖(P-Q)*cutM S‖≤ε):
    crater U P a≤ crater U Q a+ (Fintype.card I*ε + Sᶜ.card* 2)/a^2/2:=by
 let r:=1-a^2; let A:=Bolt U P a; let B:=Bolt U Q a; let W:=cutM S
 have ht:0≤r:=sub_nonneg.mpr (pow_le_one₀ e.le t)
 have hr:r<1:=by unfold r; nlinarith only [pow_pos e 2]
 have hp:‖A-1‖≤r:=span_leg q p e t; have hu:‖B-1‖≤ r:=span_leg h p e t
 have hg:‖(A-1-(B-1))*W‖≤ε:=by
    unfold A B; rw [which p,which p,←smul_sub,Algebra.smul_mul_assoc, ←sub_mul,←mul_sub,sub_sub_sub_cancel_left,←neg_sub P Q,mul_neg,neg_mul,neg_mul]; change ‖(-r) • (-(U*(P-Q)*U*W))‖≤ ε; rw [norm_smul,norm_neg r,norm_neg,Real.norm_of_nonneg ht]; refine (mul_le_of_le_one_left (norm_nonneg _) hr.le).trans ?_
    rw [mul_assoc (U*(P-Q)),v, ←mul_assoc, mul_assoc U]; exact (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (p.norm_le _)).trans ((norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (p.norm_le _)).trans f)))
 have hf:‖(A-1-(B-1))‖≤ (2:ℝ):= (norm_sub_le ..).trans ((add_le_add (hp.trans hr.le) (hu.trans hr.le)).trans_eq one_add_one_eq_two)
 have hx:= prose (fun x:Op I=>trim x (P:=A-1) (Q:=B-1) (S:=S) hg hf c) (by positivity) hp hu hr; rw [add_sub_cancel, add_sub_cancel,show 1-r=a^2 from sub_sub_cancel 1 _] at hx -- add_sub_cancel? 1+(a-1) form
 unfold crater; rw [←span_diag p q,←span_diag p h]; change Real.log ‖A.det‖/ _≤Real.log ‖B.det‖/2+_; linarith
end YM.CF.Papyrus.Granat
#print axioms YM.CF.Papyrus.Granat.hopeful

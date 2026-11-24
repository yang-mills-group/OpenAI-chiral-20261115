import YM.SU5.Relativistic.Krum
/-! # pressure & seam norm for shears -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.Franc
open Function Filter NormedSpace Fock Lattice Finset Thera
open Papyrus.Granat
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I] {P Q B:Op I} (p:IsStarProjection P)(q:IsStarProjection Q)(b:IsStarProjection B) (k:ℕ)
section
variable [Nonempty I]{r ε C:ℝ} {S: Finset I}
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
include b p q
private lemma hetrace (h:‖(P-Q)*cutM S‖≤ε) (e:0≤ε) (A:Op I) : ‖Matrix.trace (A*(lace B P-lace B Q))‖≤ ‖A‖*(Fintype.card I*ε+ Sᶜ.card*2):=by
 rw [lace, lace,←sub_mul, ←mul_sub,sub_sub_sub_cancel_left]; rw [←neg_sub P Q,mul_neg,neg_mul, mul_neg,Matrix.trace_neg,norm_neg,←mul_assoc A,Matrix.trace_mul_comm (A*_),←mul_assoc A, ←mul_assoc]
 apply (trim (B*(A*B)) h (r:=2) (by linarith only [norm_sub_le P Q, p.norm_le P,q.norm_le Q]) e).trans (mul_le_mul_of_nonneg_right _ (by positivity)); exact (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (b.norm_le _)).trans ((norm_mul_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) (b.norm_le _))))
lemma thread (h:‖(P-Q)*cutM S‖≤ε) (e:0≤ε): stunt k B P ≤ stunt k B Q + ((2*(k:ℝ)+2)*(Fintype.card I*ε+Sᶜ.card*2)) /(1-hatch k):=by
 let A:= jeans k B P; let D:= jeans k B Q; let F:= (2*(k:ℝ)+2)*(Fintype.card I*ε+Sᶜ.card*2); let d:= F/(1-hatch k)
 have hu:∀ W:Op I, ‖Matrix.trace (W*(A-1-(D-1)))‖ ≤ ‖W‖*F:=fun W=>by
    let a:= lace B P; let t:=lace B Q; have he:=fun J=> hetrace p q b h e J; let L:=2*(k:ℝ)
    rw [show A-1-(D-1)=a^(k+k+1)-t^(k+k+1)-(a-t) by unfold A D jeans; change 1-a+_ -1-(1-t+_-1)=_; abel,mul_sub,Matrix.trace_sub]
    refine (norm_sub_le ..).trans ((add_le_add (terms he (by positivity) (lemongA p b) (lemongA q b) _ _) (he W)).trans_eq ?_); unfold F; push_cast; ring
 have hw:=hatch_up k; have hp:0 ≤ F:=by unfold F; positivity
 have hh:=prose hu hp (hem_p p b k) (hem_p q b k) hw; rw [add_sub_cancel, add_sub_cancel] at hh; unfold stunt; change Real.log ‖A.det‖/ _ ≤ Real.log ‖D.det‖/2+d; change Real.log ‖A.det‖ ≤ Real.log ‖D.det‖+d at hh; have hx:0≤d:=div_nonneg hp (sub_nonneg.mpr hw.le); linarith
end
lemma je_twist (V:UNI I): Comb (twist V B) (twist V P) k=twist V (Comb B P k):=by induction k with|zero=> simp [Comb]|succ k ih=> rw [Comb,Comb,ih]; simp only [map_add,map_mul,map_sub,map_one]
lemma jv_twist (V:UNI I): jeans k (twist V B) (twist V P)=twist V (jeans k B P):=by unfold jeans lace; simp
end YM.CF.Papyrus.Franc
#print axioms YM.CF.Papyrus.Franc.thread

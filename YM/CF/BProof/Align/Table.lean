import YM.CF.BProof.Align.Hil
import YM.CF.BProof.Align.Fit
/-! Standard projection calculus on Single finite matrices. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Align
open Function Filter Fock Finset Branch
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][DecidableEq I] {P Q A:Op I}{x:Ket I}
lemma selfApply (h:IsStarProjection P) (x:Ket I) : acts P (acts P x)=acts P x:=by rw [←act_mul,h.isIdempotentElem]
lemma qrComplement (h:IsStarProjection P): (1-P)*P=0:=by rw [sub_mul,one_mul,h.isIdempotentElem,sub_self]
lemma pqComplement (h:IsStarProjection P): P*(1-P)=0:= Porth h
lemma swapOrth (h:IsStarProjection P) (q:IsStarProjection Q)(p:P*Q=0) : Q*P=0:=by rw [← h.isSelfAdjoint.star_eq,←q.isSelfAdjoint.star_eq,←star_mul,p,star_zero]
lemma projSmall (h:IsStarProjection P) (q:IsStarProjection Q)(p:P*Q=P): Q*P=P := by have ht:=congrArg star p; rw [star_mul,h.isSelfAdjoint,q.isSelfAdjoint] at ht; exact ht
lemma upCut (h:IsStarProjection P)(q:IsStarProjection Q)(p:P*Q=0): IsStarProjection (P+Q):=⟨by unfold IsIdempotentElem; rw [mul_add,add_mul,add_mul,h.isIdempotentElem,q.isIdempotentElem,p,swapOrth h q p,zero_add,add_zero], h.isSelfAdjoint.add q.isSelfAdjoint⟩
lemma subCut (h:IsStarProjection P)(q:IsStarProjection Q)(p:P*Q=P): IsStarProjection (Q-P):=⟨by unfold IsIdempotentElem; rw [mul_sub,sub_mul,sub_mul,h.isIdempotentElem,q.isIdempotentElem,p,projSmall h q p,sub_self,sub_zero], q.isSelfAdjoint.sub h.isSelfAdjoint⟩
lemma inCut (h:IsStarProjection P)(q:IsStarProjection Q)(p:P*Q=P) : P ≤ Q :=sub_nonneg.mp (subCut h q p).nonneg
lemma productZero {A:Op I}(e:P*A=A) : (1-P)*A=0:=by rw [sub_mul,one_mul,e,sub_self]
lemma inGram (h:IsStarProjection P)(q:IsStarProjection Q)(x: Ket I) : hil (P*Q*P) x= ‖acts Q (acts P x)‖^2:= by rw [← hil_idem _ q,←hil_conj,h.isSelfAdjoint.star_eq]
def hutch (A P:Op I):= P*A*P+(1-P)
lemma hutch_earn (h:IsStarProjection P){c:ℝ}(q:c • P ≤ P*A*P)(p:c≤1): c • (1:Op I) ≤ hutch A P:=by
 have g:c • (1-P) ≤1-P:=( smul_le_smul_of_nonneg_right p h.one_sub.nonneg).trans_eq (one_smul ..); apply (add_le_add q g).trans'; rw [←smul_add,add_sub_cancel]
lemma actuary(A:Op I)(x:Ket I): ‖acts A x‖≤ ‖A‖*‖x‖:=by rw [← Matrix.l2_opNorm_toEuclideanCLM]; exact ContinuousLinearMap.le_opNorm .. -- copy
lemma funded [Nonempty I] (h:IsStarProjection P)(x:Ket I): ‖acts P x‖ ≤ ‖x‖:= (actuary ..).trans (mul_le_of_le_one_left (norm_nonneg _) (h.norm_le _))
lemma act_dilate (A:Op I)(c:ℝ) (x: Ket I) : acts (c • A) x=c • (acts A x):=by rw [← Complex.coe_smul,act_smul,Complex.coe_smul]
end YM.CF.BProof.Align

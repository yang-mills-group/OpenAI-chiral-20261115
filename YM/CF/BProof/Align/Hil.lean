import Mathlib.Analysis.InnerProductSpace.Positive
import YM.CF.BProof.Align.Order
/-! Column order utilities. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Align
open Function Filter Fock Finset Branch
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][DecidableEq I] (x:Ket I){A B P:Op I}
def hil (A:Op I)(x:Ket I):= (inner ℂ (acts A x) x).re
lemma hil_mono (h:A≤B): hil A x≤ hil B x:= by
 have ht:=Matrix.isPositive_toEuclideanLin_iff.mpr (Matrix.le_iff.mp h); have he:0≤hil (B-A) x:=ht.2 x; unfold hil at *; rw [act_sub,inner_sub_left,Complex.sub_re] at he; linarith
lemma by_hil (h:IsSelfAdjoint A)(k:IsSelfAdjoint B)(p:∀ x:Ket I,hil A x≤hil B x): A≤ B:=by
 rw [Matrix.le_iff,← Matrix.isPositive_toEuclideanLin_iff]; constructor
 · exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (k.sub h)
 intro x; change 0≤ hil _ x; unfold hil; rw [act_sub,inner_sub_left,Complex.sub_re]; exact sub_nonneg.mpr (p x)
lemma hil_gram (A:Op I): hil (star A*A) x= ‖acts A x‖^2:=by unfold hil; rw [act_mul,act_inner]; exact inner_self_eq_norm_sq (𝕜:=ℂ) (acts A x)
lemma hil_idem (h:IsStarProjection P): hil P x= ‖acts P x‖^2:=by rw [←hil_gram,h.isSelfAdjoint,h.isIdempotentElem]
lemma hil_conj (P A:Op I): hil (star P*A*P) x= hil A (acts P x):=by unfold hil; rw [← show star P*(A*P)=_ from (mul_assoc ..).symm,act_mul,act_inner,act_mul]
lemma hil_linear (A:Op I)(a:ℝ) : hil (a • A) x=a*hil A x:=by unfold hil; rw [←Complex.coe_smul,act_smul,inner_smul_left]; simp
lemma hil_sum (A B:Op I) : hil (A+B) x=hil A x+hil B x:=by unfold hil; rw [act_add,inner_add_left,Complex.add_re]
lemma hil_diff (A B:Op I): hil (A-B) x=hil A x-hil B x:=by unfold hil; rw [act_sub,inner_sub_left,Complex.sub_re]
lemma hil_one : hil 1 x=‖x‖^2 := by unfold hil; rw [act_one]; exact inner_self_eq_norm_sq (𝕜:=ℂ) x
lemma splitOrth (h:IsStarProjection P) : ‖acts P x‖^2 +‖acts (1-P) x‖^2= ‖x‖^2:=by rw [←hil_idem x h,←hil_idem x h.one_sub,←hil_sum, add_sub_cancel,hil_one]
end YM.CF.BProof.Align

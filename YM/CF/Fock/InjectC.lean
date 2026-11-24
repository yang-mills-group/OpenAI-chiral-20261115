import YM.CF.Operator.Commute
import YM.CF.Fock.Pairs

/-!
# Compression is nonsingular on the occupied subspace
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Finset
attribute [local instance] opCStarAlgebra
section
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Nondegenerate pair compression. -/
def Nonsing (P C : Op n) := ∀ x : Ket n, acts (cc P) x=x → acts (P*C) x=0 → x=0
lemma nonsingSmall {P : Op n} (U : UNI n) (h : ‖P*U.val-U.val*cc P‖ < 1) : Nonsing P U.val := by
  intro x hi hk
  let A := P*U.val - U.val*cc P
  have he : ‖x‖ ≤ ‖A‖ * ‖x‖ := by
    have he : acts A x= -acts U.val x := by unfold A; rw [act_sub,hk,act_mul,hi,zero_sub]
    rw [← act_unit_norm U x,← norm_neg,← he,← Matrix.l2_opNorm_toEuclideanCLM]
    -- all occurrences
    nth_rw 2 [he]; rw [norm_neg, act_unit_norm]; exact (acts A).le_opNorm _
  by_contra g
  have hp := norm_pos_iff.mpr g
  exact (not_lt_of_ge he) ((mul_lt_mul_of_pos_right h hp).trans_eq (one_mul _))
def congrC (U : UNI n) (C : Op n) := U.val*C*U.valᵀ
lemma congr_form (U : UNI n) (C : Op n) : congrC U C=U.val*C*star (ccU U).val := by
  unfold congrC; congr 1; change _=star (cc U.val); rw [← cc_star,cc,star_star]
lemma skew_form {A C : Op n} (h : Cᵀ= -C) : (A*C*Aᵀ)ᵀ= -(A*C*Aᵀ) := by
  rw [Matrix.transpose_mul,Matrix.transpose_mul,h,Matrix.transpose_transpose,neg_mul,mul_neg,mul_assoc]
lemma congr_inv (U : UNI n) (C : Op n) : congrC (star U) (congrC U C)=C := by
  unfold congrC; change star U.val*_ * _=_; have he : star U.val * U.val=1 := U.property.1
  simp only [←mul_assoc,he,one_mul]; change C*_ * (star U.val)ᵀ=C; rw [mul_assoc, ← Matrix.transpose_mul,he,Matrix.transpose_one,mul_one]
lemma cc_twist (U : UNI n) (P : Op n) : cc (twist U P) = twist (ccU U) (cc P) := by simp only [twist_formula,cc_mul,cc_star]; rfl
lemma twist_product (U : UNI n) (P : Op n) : twist U P * U.val=U.val*P := by
  rw [twist_formula,mul_assoc,show star U.val * U.val=1 from U.property.1,mul_one]
lemma congr_product (U : UNI n) (C : Op n) : congrC U C * (ccU U).val=U.val*C := by
  rw [congr_form,mul_assoc,show star _ * (ccU U).val=1 from (ccU U).property.1,mul_one]
lemma Nonsing.twisted {P C : Op n} (h : Nonsing P C) (U : UNI n) : Nonsing (twist U P) (congrC U C) := by
  intro y e g; let V := ccU U; let x := acts (star V.val) y; have he : acts V.val x=y := act_starUnit ..
  rw [cc_twist,←he,←act_mul,show _=(V.val*cc P) from twist_product V (cc P),act_mul] at e
  rw [← he, ←act_mul,mul_assoc,show congrC U C*V.val=U.val*C from congr_product ..,← mul_assoc,twist_product,mul_assoc,act_mul] at g
  have ht : acts (cc P) x=x := by rw [← act_unit V (acts (cc P) x), e,act_unit]
  have hu : acts (P*C) x=0 := by rw [← act_unit U (acts (P*C) x),g,map_zero]
  rw [← he,h _ ht hu,map_zero]
end
end YM.CF.Fock

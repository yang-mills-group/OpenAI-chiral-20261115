import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module

/-!
# Finite one-particle conventions

The norm in CF operator lemmas is the operator norm, **not** the Frobenius norm
used in parts of YM. The order (matrix LE) is p.s.d. order.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF

open scoped MatrixOrder Matrix.Norms.L2Operator
abbrev Op (n : Type*) := Matrix n n ℂ
abbrev Ket (n : Type*) := EuclideanSpace ℂ n

variable {n : Type*} [Fintype n] [DecidableEq n]

@[implicit_reducible]
def opCStarAlgebra : CStarAlgebra (Op n) := {}
attribute [local instance] opCStarAlgebra

lemma op_le_norm_one {A : Op n} (h : IsSelfAdjoint A) : A ≤ ‖A‖ • (1 : Op n) := by
  convert! h.le_algebraMap_norm_self
  rw [Algebra.algebraMap_eq_smul_one]

lemma op_ge_neg_scalar {A : Op n} (h : IsSelfAdjoint A) {c : ℝ} (hb : ‖A‖ ≤ c) :
    -(c • (1 : Op n)) ≤ A := by
  apply neg_le_of_neg_le
  calc
    -A ≤ ‖-A‖ • (1 : Op n) := op_le_norm_one h.neg
    _ ≤ _ := by rw [norm_neg]; exact smul_le_smul_of_nonneg_right hb zero_le_one

/-- Entrywise conjugation; star on `Op` instead includes transpose. -/
def cc (A : Op n) : Op n := (star A).transpose

@[simp] lemma cc_apply (A : Op n) (x y : n) : cc A x y = star (A x y) := rfl
@[simp] lemma cc_cc (A : Op n) : cc (cc A) = A := Matrix.ext fun i j => by simp
@[simp] lemma cc_mul (A B : Op n) : cc (A*B) = cc A * cc B := by rw [cc, star_mul, Matrix.transpose_mul]; rfl
@[simp] lemma cc_star (A : Op n) : cc (star A) = star (cc A) := by ext; simp [cc]
@[simp] lemma cc_add (A B : Op n) : cc (A+B) = cc A + cc B := by ext; simp
@[simp] lemma cc_smul (a : ℂ) (A : Op n) : cc (a • A) = star a • cc A := by ext; simp
@[simp] lemma cc_rsmul (a : ℝ) (A : Op n) : cc (a • A) = a • cc A := by ext; simp
@[simp] lemma cc_neg (A : Op n) : cc (-A) = - cc A := by ext; simp
@[simp] lemma cc_sub (A B : Op n) : cc (A-B) = cc A - cc B := by rw [sub_eq_add_neg, cc_add, cc_neg, sub_eq_add_neg]
@[simp] lemma cc_zero : cc (0 : Op n) = 0 := by ext; simp
@[simp] lemma cc_one : cc (1 : Op n) = 1 := by rw [cc, star_one, Matrix.transpose_one]

/-- Norm-controlled interchange. -/
def Switch (A B : Op n) (ε : ℝ) := ‖A*B-B*A‖ ≤ ε
namespace Switch
variable {A B X Y : Op n} {e f : ℝ}
lemma symm (h : Switch A B e) : Switch B A e := by unfold Switch; rw [norm_sub_rev]; exact h
lemma add_left (h : Switch A B e) (g : Switch X B f) : Switch (A+X) B (e+f) := by
  unfold Switch
  rw [add_mul, mul_add, add_sub_add_comm]
  exact (norm_add_le ..).trans (add_le_add h g)
lemma neg_left (h : Switch A B e) : Switch (-A) B e := by
  unfold Switch
  rw [neg_mul, mul_neg, show -(A*B) - -(B*A)= -(A*B-B*A) by abel, norm_neg]
  exact h
lemma sub_left (h : Switch A B e) (g : Switch X B f) : Switch (A-X) B (e+f) := by
  rw [sub_eq_add_neg]; exact h.add_left g.neg_left
lemma smul_left (h : Switch A B e) (c : ℝ) : Switch (c • A) B (‖c‖*e) := by
  unfold Switch
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← smul_sub, norm_smul]
  exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
lemma fromCommute (h : Commute A B) : Switch A B 0 := by simp [Switch,h.eq]
lemma star_star (h : Switch A B e) : Switch (star A) (star B) e := by
  unfold Switch
  rw [← star_mul, ← star_mul, ← star_sub, norm_star]
  exact h.symm
lemma star_left [Nonempty n] (h : Switch A B e) (ha : A ∈ unitary (Op n)) :
    Switch (star A) B e := by
  unfold Switch
  have he : ‖star A‖ = 1 := by rw [norm_star, CStarRing.norm_of_mem_unitary ha]
  have h₁ : A * star A = 1 := ha.2
  have h₂ : star A * A = 1 := ha.1
  rw [show star A*B-B*star A = star A*(B*A-A*B)*star A by
    rw [mul_sub, sub_mul, ← mul_assoc (star A) B A, mul_assoc (star A * B) A (star A), h₁,
      mul_one, ← mul_assoc (star A) A B, h₂, one_mul]
  ]
  exact (norm_mul_le ..).trans (by
    rw [he, mul_one]
    exact (norm_mul_le ..).trans (by rw [he, one_mul]; exact h.symm))
end Switch

end YM.CF

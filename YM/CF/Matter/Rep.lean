import YM.CF.Matter.Det
import YM.CF.Operator.Commute
import YM.Gauge.MatrixGroup

/-!
# Actual gauge group and representation

Use a single copy of this gauge and the Wilson action in the faithful defining
representation. Compact matrix gauge conventions from YM; SU itself, not PSU.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF
open scoped Matrix.Norms.L2Operator Topology Matrix Kronecker
attribute [local instance] opCStarAlgebra
namespace SU
abbrev F := Fin 5
abbrev Ten := ExTwo.Idx F
abbrev Sheet := Ten ⊕ F
abbrev Slot := Fin 3 × Sheet

lemma pairs : Fintype.card Ten = 10 := by decide
lemma slots : Fintype.card Slot = 45 := by simp [Slot,Sheet,pairs,F]

def image : Subgroup (UNI F) where
  carrier := {U | U.val.det=1}
  one_mem' := Matrix.det_one
  mul_mem' := fun {u v} h k => by
    change ((_:Op F)*_).det = _; rw [Matrix.det_mul, show Matrix.det u.val=1 from h, show Matrix.det v.val=1 from k,mul_one]
  inv_mem' := fun {u} h => by
    change Matrix.det (star _) = 1
    rw [Matrix.star_eq_conjTranspose,Matrix.det_conjTranspose, show Matrix.det u.val=1 from h,star_one]

def group : Gauge where
  n := 4
  imageGroup := image
  closed_imageGroup := by
    change IsClosed {U : UNI F | U.val.det=1}; exact isClosed_eq continuous_subtype_val.matrix_det continuous_const

abbrev E := group.El
def fund (U : E) : Op F := group.mat U
lemma fund_det (U : E) : (fund U).det=1 := U.property
lemma fund_U (U : E) : fund U ∈ unitary (Op F) := U.val.property
lemma fund_cont : Continuous fund := group.continuous_mat
lemma fund_mul (U V:E) : fund (U*V)=fund U*fund V := rfl
lemma fund_inv (U:E) : fund U⁻¹=star (fund U) := rfl
lemma fund_one : fund 1=1 := rfl
end SU

-- block operations shared by copies and one-generation actions
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
namespace Join
def both (A : Op n) (B : Op m) : Op (n⊕m) := Matrix.fromBlocks A 0 0 B
lemma star_both (A : Op n) (B : Op m) : star (both A B)=both (star A) (star B) := by
  simp only [Matrix.star_eq_conjTranspose,both,Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero]
lemma both_mul (A C : Op n) (B D : Op m) : both A B*both C D = both (A*C) (B*D) := by simp [both,Matrix.fromBlocks_multiply]
lemma both_one : both (1 : Op n) (1 : Op m) = 1 := by simp [both]
lemma both_det (A : Op n) (B : Op m) : (both A B).det=A.det*B.det := by rw [both,Matrix.det_fromBlocks_zero₁₂]
lemma both_unitary {A : Op n} {B : Op m} (h : A ∈ unitary (Op n)) (g : B ∈ unitary (Op m)) : both A B ∈ unitary _ := by
  constructor
  · rw [star_both,both_mul,show star A * A = 1 from h.1,show star B * B = 1 from g.1,both_one]
  rw [star_both,both_mul,show A * star A = 1 from h.2, show B * star B=1 from g.2,both_one]
end Join

namespace SU
open Join ExTwo
/-- Off the group, useful also as a smooth function. -/
def each (A : Op F) : Op Sheet := both (wedgeOp A) (cc A)
def triple (A : Op F) : Op Slot := (1:Op (Fin 3)) ⊗ₖ each A
lemma each_one : each 1 = 1 := by rw [each,cc_one,wedge_one,both_one]
lemma triple_one : triple 1=1 := by rw [triple,each_one,Matrix.one_kronecker_one]
lemma each_star (A) : each (star A)=star (each A) := by simp only [each,wedge_star, star_both, cc_star]
lemma each_mul (A B) : each (A*B)=each A*each B := by simp only [each,wedge_mul,both_mul,cc_mul]
lemma triple_star (A) : triple (star A)=star (triple A) := by simp only [triple,each_star,op_star_kron, star_one]
lemma triple_mul (A B) : triple (A*B)=triple A*triple B := by simp only [triple,each_mul,op_kron_mul,mul_one]
lemma each_mem (U : E) : each (fund U) ∈ unitary (Op Sheet) := by
  constructor <;> rw [← each_star,← each_mul, show _*_=(1:Op F) by first | exact (fund_U U).1 | exact (fund_U U).2, each_one]
lemma each_det (U : E) : (each (fund U)).det=1 := by
  rw [each, both_det, cc, Matrix.det_transpose, Matrix.star_eq_conjTranspose,Matrix.det_conjTranspose,wedge_det,fund_det]; simp
lemma triple_mem (U : E) : triple (fund U) ∈ unitary (Op Slot) := by
  constructor <;> rw [← triple_star,← triple_mul, show _*_=(1:Op F) by first | exact (fund_U U).1 | exact (fund_U U).2, triple_one]
lemma triple_det (U : E) : (triple (fund U)).det=1 := by rw [triple,Matrix.det_kronecker,Matrix.det_one,each_det]; simp

/-- Weyl matter (all copies). -/
def matter : E →* UNI Slot where
  toFun U := ⟨triple (fund U), triple_mem U⟩
  map_mul' U V := Subtype.ext (triple_mul (fund U) (fund V))
  map_one' := Subtype.ext triple_one
@[simp] lemma matter_matrix (U : E) : (matter U).val=triple (fund U) := rfl
lemma each_cont : Continuous each := by
  apply continuous_matrix; intro i j; cases i <;> cases j <;> simp only [each,both, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,wedge_entry,cc_apply] <;> fun_prop
lemma triple_cont : Continuous triple := by
  apply continuous_matrix
  rintro ⟨x,i⟩ ⟨y,j⟩; simp only [triple,Matrix.kronecker_apply]; exact continuous_const.mul (each_cont.matrix_elem i j)
lemma matter_cont : Continuous (fun x => (matter x).val) := triple_cont.comp fund_cont
end SU
end YM.CF

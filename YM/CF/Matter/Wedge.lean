import YM.CF.Operator.Blocks

/-! The two-box antisymmetric representation (not a name for an abstract slot).
Coordinates are increasing pairs. `wedgeTensor` below identifies it with the
antisymmetric tensor subrepresentation. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.ExTwo
open scoped Matrix Kronecker
open Finset
variable {n : Type*} [Fintype n] [LinearOrder n]
abbrev Idx (n : Type*) [LT n] := {z : n × n // z.1 < z.2}

def wedgeOp (A : Op n) : Op (Idx n) := Matrix.of fun i j =>
  A i.val.1 j.val.1 * A i.val.2 j.val.2 - A i.val.1 j.val.2 * A i.val.2 j.val.1
lemma wedge_entry (A : Op n) (i j : Idx n) :
    wedgeOp A i j = A i.val.1 j.val.1*A i.val.2 j.val.2-A i.val.1 j.val.2*A i.val.2 j.val.1 := rfl

/-- Columns antisymmetric, squared norm two each. -/
def Q (n : Type*) [LT n] [DecidableEq n] : Matrix (n × n) (Idx n) ℂ := Matrix.of fun x i =>
  (if x = i.val then 1 else 0)-(if x=i.val.swap then 1 else 0)
lemma insert_q (x : Idx n) (y:Idx n) : Q n x.val y = if x=y then 1 else 0 := by
  have h : x.val≠y.val.swap := fun he => y.property.asymm (show _ from by
    have H := x.property; rw [he] at H; exact H)
  by_cases e:x=y
  · subst y; simp [Q,h]
  have hi : x.val≠y.val := fun he => e (Subtype.ext he)
  simp only [Q, Matrix.of_apply,if_neg hi, if_neg h, sub_zero,if_neg e]
lemma swap_q (x : n×n) (y : Idx n) : Q n x.swap y = -Q n x y := by
  simp only [Q,Matrix.of_apply, show (x.swap=y.val)=(x=y.val.swap) from propext
    ⟨fun h => by rw [← h]; rfl, fun h => by rw [h]; rfl⟩, Prod.swap_inj]; abel
lemma multiply_q {m : Type*} (A : Matrix m (n×n) ℂ) (x:m) (p:Idx n) :
    (A*Q n) x p = A x p.val - A x p.val.swap := by
  simp only [Matrix.mul_apply, Q,Matrix.of_apply,mul_sub,mul_ite,mul_one,mul_zero,sum_sub_distrib,
    sum_ite_eq', mem_univ, if_true]
lemma multiply_qdag {m : Type*} (A : Matrix (n×n) m ℂ) (p:Idx n) (y:m) :
    ((Q n)ᴴ*A) p y = A p.val y-A p.val.swap y := by
  simp [Matrix.mul_apply,Q,star_sub,sub_mul,ite_mul,sum_sub_distrib]
lemma q_read {m : Type*} (A : Matrix (Idx n) m ℂ) (p:Idx n) (x:m) :
    (Q n*A) p.val x=A p x := by simp [Matrix.mul_apply,insert_q,ite_mul]
lemma q_swap {m : Type*} (A : Matrix (Idx n) m ℂ) (z:n × n) (x:m) :
    (Q n*A) z.swap x= -(Q n*A) z x := by
  simp only [Matrix.mul_apply, swap_q z,neg_mul,sum_neg_distrib]
lemma q_inner : (Q n)ᴴ * Q n = (2:ℂ) • (1:Op (Idx n)) := by
  ext x y
  rw [multiply_q,Matrix.conjTranspose_apply,Matrix.conjTranspose_apply,insert_q,
    swap_q y.val,insert_q]; by_cases h:x=y <;> norm_num [eq_comm (a:=y), h, Matrix.one_apply]

private lemma eq_zero_complex {x : ℂ} (h : x= -x) : x=0 := by
  apply mul_left_cancel₀ (show (2:ℂ) ≠ 0 by norm_num)
  rw [mul_zero,two_mul]; exact eq_neg_iff_add_eq_zero.mp h

/-- Coordinate embedding intertwines the tensor-square representation. -/
lemma wedgeTensor (A : Op n) : A ⊗ₖ A * Q n = Q n * wedgeOp A := by
  have h (x : Idx n) (y) : (A ⊗ₖ A * Q n) x.val y = (Q n * wedgeOp A) x.val y := by
    rw [q_read,multiply_q]; simp [wedge_entry]
  have e (x : n×n) (y) : (A ⊗ₖ A * Q n) x.swap y = -((A ⊗ₖ A * Q n) x y) := by
    rw [multiply_q,multiply_q]; simp only [Matrix.kroneckerMap_apply,Prod.fst_swap,Prod.snd_swap]; ring
  ext ⟨i,j⟩ y
  rcases lt_trichotomy i j with hi|hi|hi
  · exact h ⟨(i,j),hi⟩ y
  · subst i; have hz₁ := q_swap (wedgeOp A) (j,j) y; have hz₂ := e (j,j) y
    simp only [Prod.swap_prod_mk] at hz₁ hz₂
    rw [eq_zero_complex hz₁, eq_zero_complex hz₂]
  change (A ⊗ₖ A * Q n) (j,i).swap y = (Q n * wedgeOp A) (j,i).swap y
  rw [e, q_swap, show (A ⊗ₖ A * Q n) (j,i) y=(Q n*wedgeOp A) (j,i) y from h ⟨(j,i),hi⟩ y]

lemma q_inj {m : Type*} {A B : Matrix (Idx n) m ℂ} (h : Q n * A = Q n * B) : A=B := by
  ext x y; rw [← q_read A x y, h, q_read]
lemma wedge_mul (A B : Op n) : wedgeOp (A*B)=wedgeOp A*wedgeOp B := by
  apply q_inj
  rw [← wedgeTensor, ← Matrix.mul_assoc, ← wedgeTensor, ← op_kron_mul A, Matrix.mul_assoc, wedgeTensor, Matrix.mul_assoc]
lemma wedge_star (A : Op n) : wedgeOp (star A)=star (wedgeOp A) := by ext; simp [wedge_entry,mul_comm]
lemma wedge_one : wedgeOp (1 : Op n) = 1 := q_inj (by rw [← wedgeTensor, Matrix.one_kronecker_one, Matrix.one_mul, Matrix.mul_one])
lemma wedge_mem {A : Op n} (h : A ∈ unitary (Op n)) : wedgeOp A ∈ unitary (Op (Idx n)) := by
  constructor <;> rw [← wedge_star, ← wedge_mul, show _*_=(1:Op n) by first | exact h.1 | exact h.2, wedge_one]

/-- Tensor flip. -/
def flipOp (n : Type*) [DecidableEq n] : Op (n × n) := Matrix.of fun i j => if i.swap=j then 1 else 0
lemma flip_left {m : Type*} (A : Matrix (n×n) m ℂ) (x y) : (flipOp n * A) x y = A x.swap y := by
  simp [Matrix.mul_apply, flipOp, ite_mul]
lemma flip_right {m : Type*} (A : Matrix m (n×n) ℂ) (x y) : (A*flipOp n) x y = A x y.swap := by
  simp only [Matrix.mul_apply, flipOp, Matrix.of_apply,
    show ∀ i : n×n, (i.swap=y)=(i=y.swap) from fun i => propext ⟨fun h => by rw [← h]; rfl, fun h => by rw [h]; rfl⟩, mul_ite, mul_one, mul_zero,
    sum_ite_eq', mem_univ, if_true]
lemma flip_sq : flipOp n * flipOp n = 1 := by
  ext x y; rw [flip_left]; simp [flipOp,Matrix.one_apply]
lemma q_span : Q n * (Q n)ᴴ = (1:Op (n×n))-flipOp n := by
  have h (x : Idx n) (z) : (Q n*(Q n)ᴴ) x.val z = ((1:Op (n×n))-flipOp n) x.val z := by
    rw [q_read]; simp [Matrix.one_apply,flipOp,Q, eq_comm]
  have ht (x z : n×n) : ((1:Op (n×n))-flipOp n) x.swap z = -(((1:Op (n×n))-flipOp n) x z) := by
    simp only [Matrix.sub_apply,Matrix.one_apply,flipOp,Matrix.of_apply,Prod.swap_swap]; abel
  ext ⟨i,j⟩ z
  rcases lt_trichotomy i j with hi|hi|hi
  · exact h ⟨(i,j),hi⟩ z
  · subst i; have hz₁ := q_swap (Q n)ᴴ (j,j) z; have hz₂ := ht (j,j) z
    simp only [Prod.swap_prod_mk] at hz₁ hz₂
    rw [eq_zero_complex hz₁, eq_zero_complex hz₂]
  change (Q n * (Q n)ᴴ) (j,i).swap z = ((1:Op (n×n))-flipOp n) (j,i).swap z
  rw [q_swap, ht, show (Q n*(Q n)ᴴ) (j,i) z= _ from h ⟨(j,i),hi⟩ z]
end YM.CF.ExTwo

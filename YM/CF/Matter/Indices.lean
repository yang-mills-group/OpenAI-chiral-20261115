import YM.CF.Matter.Rep

/-! Infinitesimal representation and local polynomial tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.ExTwo
open scoped Matrix.Norms.L2Operator Matrix Kronecker BigOperators
attribute [local instance] opCStarAlgebra
variable {n : Type*} [Fintype n] [LinearOrder n]

def current (A : Op n) : Op (n × n) := A ⊗ₖ (1: Op n) + (1:Op n) ⊗ₖ A
def readQ (B : Op (n × n)) := (1/2:ℂ) • ((Q n)ᴴ*B*Q n)
def gen (A : Op n) := readQ (current A)

lemma flip_kron (A B : Op n) : Commute (flipOp n) (A ⊗ₖ B + B ⊗ₖ A) := by
  rw [Commute,SemiconjBy]; ext ⟨i,j⟩ ⟨k,l⟩; rw [flip_left,flip_right]; simp; ring
lemma flip_current (A : Op n) : Commute (flipOp n) (current A) := flip_kron ..
lemma gen_tensor (A : Op n) : Q n * gen A = current A * Q n := by
  unfold gen readQ
  have hs := Commute.sub_left (Commute.one_left (current A)) (flip_current A)
  rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, q_span, hs.eq,
    ← q_span, Matrix.mul_assoc, Matrix.mul_assoc, q_inner, Matrix.mul_smul, Matrix.mul_smul,
    smul_smul]
  norm_num
lemma gen_pow_tensor (A : Op n) (k : ℕ) : Q n * gen A ^ k = current A ^ k * Q n := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ,pow_succ, ← Matrix.mul_assoc, ih,Matrix.mul_assoc,gen_tensor, ← Matrix.mul_assoc]
lemma reread {X : Op (Idx n)} {B : Op (n×n)} (h : B*Q n = Q n*X) : readQ B=X := by
  rw [readQ,Matrix.mul_assoc,h, ← Matrix.mul_assoc,q_inner,Matrix.smul_mul,smul_smul]; norm_num
lemma gen_pow_read (A : Op n) (k : ℕ) : gen A ^ k = readQ (current A ^ k) := (reread (gen_pow_tensor A k).symm).symm
lemma trace_read (B : Op (n×n)) : (readQ B).trace=(B.trace-(B*flipOp n).trace)/2 := by
  rw [readQ, Matrix.trace_smul, Matrix.trace_mul_cycle, q_span, Matrix.trace_mul_comm, mul_sub, mul_one, Matrix.trace_sub, smul_eq_mul]; ring
lemma trace_swap (A B : Op n) : ((A ⊗ₖ B)*flipOp n).trace=(A*B).trace := by
  simp only [Matrix.trace,Matrix.diag_apply,Fintype.sum_prod_type,flip_right]
  simp [Matrix.mul_apply]
lemma trace_tensor (A B : Op n) : (A ⊗ₖ B).trace=A.trace*B.trace := Matrix.trace_kronecker ..
lemma kr_mul (A B C D : Op n) : A ⊗ₖ B * C ⊗ₖ D = (A*C) ⊗ₖ (B*D) := op_kron_mul ..
lemma trace_gen (A : Op n) : (gen A).trace = (Fintype.card n-1:ℂ)*A.trace := by
  rw [gen, trace_read]; unfold current
  rw [Matrix.trace_add,trace_tensor,trace_tensor,add_mul,Matrix.trace_add,trace_swap,trace_swap,one_mul,mul_one,Matrix.trace_one]; ring
lemma quad_gen (A : Op n) : (gen A ^ 2).trace = (Fintype.card n-2:ℂ)*(A^2).trace + A.trace^2 := by
  rw [gen_pow_read,trace_read, sq, sq]
  simp only [current,Matrix.trace_add,trace_tensor, Matrix.trace_one, add_mul, mul_add,Matrix.trace_add,trace_swap,
    kr_mul, one_mul,mul_one]; ring
lemma cubic_gen (A : Op n) : (gen A ^ 3).trace = (Fintype.card n-4:ℂ)*(A^3).trace + 3*A.trace*(A^2).trace := by
  rw [gen_pow_read,trace_read]
  simp only [pow_succ,pow_zero, current,one_mul,Matrix.trace_add,trace_tensor,Matrix.trace_one,add_mul,mul_add,
    Matrix.trace_add,trace_swap,kr_mul,one_mul,mul_one,mul_assoc]
  ring
end YM.CF.ExTwo

import YM.CF.Operator.Basic

/-! Finite one-particle space helpers. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker BigOperators
open Finset
attribute [local instance] opCStarAlgebra
variable {X n : Type*} [Fintype X] [DecidableEq X] [Fintype n] [DecidableEq n]
set_option linter.unusedSectionVars false

abbrev acts (A : Op n) : Ket n →L[ℂ] Ket n := Matrix.toEuclideanCLM (n:=n) (𝕜:=ℂ) A

lemma act_at (A : Op n) (v : Ket n) (i) : (acts A v).ofLp i = (A *ᵥ v.ofLp) i := rfl
lemma norm_entry (A : Op n) (i j) : ‖A i j‖ ≤ ‖A‖ := by
  let v := EuclideanSpace.single j (1:ℂ)
  have ht : ‖acts A v‖ ≤ ‖A‖ := by
    calc
      _ ≤ _ := (acts A).le_opNorm v
      _ = _ := by rw [acts, Matrix.l2_opNorm_toEuclideanCLM,show ‖v‖ = 1 from by simp [v], mul_one]
  apply le_trans _ ht
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq]
  have hb : (acts A v).ofLp i = A i j := by rw [act_at]; simp [v]
  simpa [hb] using (Finset.single_le_sum (f:=fun k => ‖(acts A v).ofLp k‖^2) (fun k _ => sq_nonneg _) (Finset.mem_univ i))

def jump (f : Equiv.Perm X) (J : X → Op n) : Op (X × n) := Matrix.of fun x y =>
    if f x.1=y.1 then J x.1 x.2 y.2 else 0
lemma jump_apply (f : Equiv.Perm X) (J : X → Op n) (x y) :
    jump f J x y = if f x.1=y.1 then J x.1 x.2 y.2 else 0 := rfl
lemma jump_mul (f g : Equiv.Perm X) (A B : X → Op n) : jump f A * jump g B =
    jump (f.trans g) (fun x => A x * B (f x)) := by
  ext ⟨x,i⟩ ⟨y,j⟩
  simp only [Matrix.mul_apply, jump_apply, Equiv.trans_apply]
  rw [Fintype.sum_prod_type]
  rw [sum_eq_single (f x)]
  · by_cases h:g (f x)=y <;> simp [h]
  · intro b _ hb; simp [Ne.symm hb]
  simp
lemma jump_star (f : Equiv.Perm X) (A : X → Op n) : star (jump f A) = jump f.symm (fun x => star (A (f.symm x))) := by
  ext ⟨x,i⟩ ⟨y,j⟩
  by_cases h : f y=x
  · subst x; simp [jump_apply]
  have he : f.symm x ≠ y := by rw [Ne,Equiv.symm_apply_eq,eq_comm]; exact h
  simp [jump_apply,h,he]
lemma jump_cc (f : Equiv.Perm X) (A : X → Op n) : cc (jump f A) = jump f (fun x => cc (A x)) := by
  ext ⟨x,i⟩ ⟨y,j⟩; by_cases h : f x=y <;> simp [jump_apply,h]
lemma jump_add (f : Equiv.Perm X) (A B : X → Op n) : jump f (A+B) = jump f A + jump f B := by
  ext ⟨x,i⟩ ⟨y,j⟩; by_cases h:f x=y <;> simp [jump_apply,h]
lemma jump_sub (f : Equiv.Perm X) (A B : X → Op n) : jump f (A-B) = jump f A - jump f B := by
  ext ⟨x,i⟩ ⟨y,j⟩; by_cases h:f x=y <;> simp [jump_apply,h]
lemma jump_neg (f : Equiv.Perm X) (A : X → Op n) : jump f (fun x => -A x) = -jump f A := by
  ext ⟨x,i⟩ ⟨y,j⟩; by_cases h:f x=y <;> simp [jump_apply,h]
lemma jump_smul (f : Equiv.Perm X) (A : X → Op n) (c : ℂ) : jump f (c • A) = c • jump f A := by
  ext ⟨x,i⟩ ⟨y,j⟩; by_cases h:f x=y <;> simp [jump_apply,h]
lemma jump_id : jump (Equiv.refl X) (fun _ => (1 : Op n)) = 1 := by
  ext ⟨x,i⟩ ⟨y,j⟩; by_cases h:x=y <;> simp [jump_apply,h,Matrix.one_apply]
lemma jump_unitary (f : Equiv.Perm X) (J : X → Op n) (h : ∀ x, J x ∈ unitary (Op n)) :
    jump f J ∈ unitary (Op (X × n)) := by
  constructor <;> rw [jump_star,jump_mul, ← jump_id]
  · simp only [Equiv.symm_trans_self]; congr; funext x; exact (h _).1
  simp only [Equiv.self_trans_symm, Equiv.symm_apply_apply]; congr; funext x; exact (h _).2

def portion (v : Ket (X × n)) (x : X) : Ket n := WithLp.toLp 2 (fun i => v.ofLp (x,i))
lemma portions (v : Ket (X × n)) : ‖v‖ ^ 2 = ∑ x, ‖portion v x‖^2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  apply sum_congr rfl; intro x _; exact (EuclideanSpace.norm_sq_eq (portion v x)).symm
lemma act_jump (f : Equiv.Perm X) (J : X → Op n) (v : Ket (X×n)) (x) :
    portion (acts (jump f J) v) x = acts (J x) (portion v (f x)) := by
  apply PiLp.ext; intro i
  change (acts (jump f J) v).ofLp _ = _; rw [act_at]
  change (jump f J *ᵥ _) _ = (J x *ᵥ _) _
  simp only [Matrix.mulVec, dotProduct, jump_apply, Fintype.sum_prod_type]
  rw [sum_eq_single (f x)]
  · simp [portion]
  · intro b _ hb; simp [Ne.symm hb]
  simp
lemma jump_bound (f : Equiv.Perm X) (J : X → Op n) {b : ℝ} (hb : 0 ≤ b) (h : ∀ x, ‖J x‖ ≤ b) :
    ‖jump f J‖ ≤ b := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ hb
  intro v
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity),mul_pow,portions,portions,
    ← Equiv.sum_comp f (fun x => ‖portion v x‖^2), mul_sum]
  apply sum_le_sum; intro x _
  change ‖portion (acts _ v) _‖ ^ 2 ≤ _
  rw [act_jump,← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) ((ContinuousLinearMap.le_opNorm ..).trans <|
    mul_le_mul_of_nonneg_right (by rw [acts, Matrix.l2_opNorm_toEuclideanCLM]; exact h x) (norm_nonneg _)) _
lemma jump_replicate (A : Op n) : jump (Equiv.refl X) (fun _ => A) = (1 : Op X) ⊗ₖ A := by
  ext ⟨x,i⟩ ⟨y,j⟩; by_cases h:x=y <;> simp [jump_apply,h]
lemma replicas_bound (A : Op n) : ‖(1 : Op X) ⊗ₖ A‖ ≤ ‖A‖ :=
  by rw [← jump_replicate]; exact jump_bound _ _ (norm_nonneg _) (fun _ => le_rfl)

lemma op_star_kron (A : Op X) (B : Op n) : star (A ⊗ₖ B) = star A ⊗ₖ star B :=
  Matrix.conjTranspose_kronecker ..
lemma op_cc_kron (A : Op X) (B : Op n) : cc (A ⊗ₖ B) = cc A ⊗ₖ cc B := by
  ext ⟨x,i⟩ ⟨y,j⟩; simp
lemma op_kron_mul (A C : Op X) (B D : Op n) : A ⊗ₖ B * C ⊗ₖ D = (A*C) ⊗ₖ (B*D) :=
  (Matrix.mul_kronecker_mul ..).symm
lemma op_kron_smul (A : Op X) (B : Op n) (c : ℂ) : A ⊗ₖ (c • B) = c • (A ⊗ₖ B) := by
  ext ⟨x,i⟩ ⟨y,j⟩; simp [mul_left_comm]
lemma op_kron_sub (A : Op X) (B C : Op n) : A ⊗ₖ (B-C) = A ⊗ₖ B - A ⊗ₖ C := by
  ext ⟨x,i⟩ ⟨y,j⟩; simp [mul_sub]
lemma op_kron_neg (A : Op X) (B : Op n) : (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext ⟨x,i⟩ ⟨y,j⟩; simp
end YM.CF

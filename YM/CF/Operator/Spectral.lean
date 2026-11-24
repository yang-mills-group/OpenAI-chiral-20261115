import YM.CF.Operator.Basic

/-! Convenient names for explicit spectral computations. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n : Type*} [Fintype n] [DecidableEq n]
attribute [local instance] opCStarAlgebra
abbrev UNI (n : Type*) [Fintype n] [DecidableEq n] := ↥(unitary (Op n))

def twist (U : UNI n) : Op n ≃⋆ₐ[ℝ] Op n := Unitary.conjStarAlgAut ℝ _ U
lemma twist_formula (U : UNI n) (A : Op n) : twist U A = U.val*A*star U.val := Unitary.conjStarAlgAut_apply ..
lemma twist_norm (U : UNI n) (A : Op n) : ‖twist U A‖ = ‖A‖ := by
  rw [twist_formula]; change ‖(U:Op n)*A*((star U : UNI n): Op n)‖ = _
  rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]
lemma twist_inv (U : UNI n) (A : Op n) : twist (star U : UNI n) (twist U A) = A := by
  rw [twist_formula, twist_formula]
  change star U.val * (U.val * A * star U.val) * star (star U.val) = A
  rw [star_star]
  have h : star U.val * U.val = 1 := U.property.1
  simp only [← mul_assoc,h,one_mul]; rw [mul_assoc,h,mul_one]
lemma twist_mono (U : UNI n) : Monotone (twist U) := fun x y h => by
  rw [twist_formula, twist_formula]; exact star_right_conjugate_le_conjugate h _
lemma twist_le_twist (U : UNI n) (A B : Op n) : twist U A ≤ twist U B ↔ A ≤ B := by
  refine ⟨fun h => ?_, fun h => twist_mono U h⟩
  simpa only [twist_inv] using twist_mono (star U) h

/-- Real diagonal in a unitary frame. -/
def spectral (U : UNI n) (d : n → ℝ) : Op n := twist U (Matrix.diagonal fun i => (d i : ℂ))
lemma spectral_exists (A : Op n) (h : IsSelfAdjoint A) : ∃ U d, A = spectral U d :=
  let e : Matrix.IsHermitian A := Matrix.isHermitian_iff_isSelfAdjoint.mpr h
  ⟨e.eigenvectorUnitary,e.eigenvalues,e.spectral_theorem⟩
lemma spectral_adjoint (U : UNI n) (d : n → ℝ) : IsSelfAdjoint (spectral U d) := by
  rw [isSelfAdjoint_iff,spectral,← map_star]
  apply congrArg (twist U)
  ext i j; by_cases h : i=j
  · subst j; simp
  simp [h,Ne.symm h]
lemma spectral_add (U : UNI n) (d e : n → ℝ) : spectral U d + spectral U e = spectral U (d+e) := by
  simp only [spectral, ← map_add,Matrix.diagonal_add, Pi.add_apply, Complex.ofReal_add]
lemma spectral_sub (U : UNI n) (d e : n → ℝ) : spectral U d - spectral U e = spectral U (d-e) := by
  simp only [spectral, ← map_sub,Matrix.diagonal_sub, Pi.sub_apply,Complex.ofReal_sub]
lemma spectral_mul (U : UNI n) (d e : n → ℝ) : spectral U d * spectral U e = spectral U (d*e) := by
  simp only [spectral, ← map_mul,Matrix.diagonal_mul_diagonal, Pi.mul_apply,Complex.ofReal_mul]
lemma spectral_zero (U : UNI n) : spectral U 0 = 0 := by simp [spectral]
lemma spectral_one (U : UNI n) : spectral U 1 = 1 := by simp [spectral]
lemma spectral_pow (U : UNI n) (d : n → ℝ) (k : ℕ) : spectral U d ^ k = spectral U (d^k) := by
  induction k with
  | zero => rw [pow_zero,pow_zero,spectral_one]
  | succ k ih => rw [pow_succ,pow_succ,ih,spectral_mul]
lemma spectral_smul (U : UNI n) (c : ℝ) (d : n → ℝ) : c • spectral U d = spectral U (c • d) := by
  rw [spectral, ← map_smul]
  unfold spectral
  apply congrArg (twist U)
  ext i j; by_cases h : i=j
  · subst j; simp [Complex.real_smul]
  simp [h]
open scoped ComplexOrder in
lemma spectral_le (U : UNI n) (d e : n → ℝ) : spectral U d ≤ spectral U e ↔ d ≤ e := by
  rw [← sub_nonneg,spectral_sub, ← spectral_zero U]
  unfold spectral
  rw [twist_le_twist]; simp only [Pi.zero_apply, Complex.ofReal_zero]
  rw [show (Matrix.diagonal (fun _ : n => (0:ℂ))) = 0 by simp, Matrix.nonneg_iff_posSemidef,
    Matrix.posSemidef_diagonal_iff]
  simp [Pi.le_def]
end YM.CF

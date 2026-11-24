import YM.CF.Fock.Semig

/-!
# One extensive (rank-additive) dΓ bill

`Graph.sedge` uses dimension-squared on the ONE-PARTICLE space, which can give
an exponential-**super**extensive bound on the corresponding Fock exp,
unusable for even a simple volume comparison. Prefer the entry bills of `Toy`
which sum extensively. But we cannot just bound `entryBudget` after a change
of basis, a star projection etc by the same entry bill. Prove a bound that
lets us apply the entry estimate BEFORE such operations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Function Finset Fock NormedSpace
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I : Type*} [Fintype I] [LinearOrder I]

def entryBudget (U : Op I) : ℝ := ∑ i, ∑ j, ‖U i j‖
omit [LinearOrder I] in
lemma entryBudget_ge (U : Op I) : 0 ≤ entryBudget U :=
  sum_nonneg fun _ _=>sum_nonneg fun _ _=>norm_nonneg _
omit [LinearOrder I] in
lemma entryBudget_adjoint (U : Op I) : entryBudget (star U)=entryBudget U := by
  unfold entryBudget; simp_rw [Matrix.star_apply,norm_star]; exact sum_comm

lemma generator_zero : dg (0 : Op I)=0 := by unfold dg dyad; simp
lemma generator_smul (A : Op I) (c : ℂ) : dg (c • A)=c • dg A := by
  unfold dg dyad; simp only [Matrix.smul_apply,smul_assoc,smul_sum]
lemma generator_sum {α : Type*} (F : Finset α) (K : α→Op I) :
    dg (∑ i∈F,K i)=∑ i∈F,dg (K i) := by
  classical induction F using Finset.induction_on with
  | empty=> rw [sum_empty,sum_empty]; exact generator_zero
  | insert i t h ih=> rw [sum_insert h,sum_insert h,dg_add,ih]

-- From Flare.cost_pe proof (`YM/CF/Flare/Wits`), avoiding huge imports.
private lemma create_le (u : Ket I) : ‖create u‖ ≤ ‖u‖ := by
  rw [←Matrix.l2_opNorm_toEuclideanCLM]; apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _); intro z
  let U := create u; let V := remove u; let P := acts U z; let W := acts V z
  have hx : ‖P‖^2 + ‖W‖^2 = ‖u‖^2 * ‖z‖^2 := by
    rw [← inner_self_eq_norm_sq (𝕜:=ℂ), ← inner_self_eq_norm_sq (𝕜:=ℂ),← map_add]
    rw [show inner ℂ P P = inner ℂ z (acts (V*U) z) by rw [act_mul,←act_inner V z (acts U z), show star V=U from star_star _],
        show inner ℂ W W = inner ℂ z (acts (U*V) z) by rw [act_mul, ← act_inner U z (acts V z)],
        ←inner_add_right, ←act_add,car,act_smul,act_one,inner_smul_right]
    simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
  refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).1 ?_
  rw [mul_pow, ← hx]; exact le_add_of_nonneg_right (sq_nonneg _)
private lemma col_le (V : Op I) (x : I) : ‖acts V (basisKet x)‖ ≤ ‖V‖ :=
  ((acts V).le_opNorm _).trans_eq (by simp [Matrix.l2_opNorm_toEuclideanCLM,basisKet,acts])

lemma extensiveDG (A B X : Op I) : ‖dg (A*X*star B)‖ ≤ entryBudget X*(‖A‖*‖B‖) := by
  unfold dg; rw [← ccT B, ← dyad_prong]
  unfold dyad; simp_rw [prong_t, prong_p]
  refine (norm_sum_le ..).trans ?_
  unfold entryBudget; rw [sum_mul]; apply sum_le_sum; intro i _
  refine (norm_sum_le ..).trans ?_; rw [sum_mul]; apply sum_le_sum; intro j _; rw [norm_smul]
  refine mul_le_mul_of_nonneg_left ((norm_mul_le ..).trans ?_) (norm_nonneg _)
  refine mul_le_mul ((create_le _).trans (col_le A i)) ?_ (norm_nonneg _) (norm_nonneg _)
  unfold remove; rw [norm_star]; exact (create_le _).trans (col_le B j)

lemma extensiveDG' (A B X : Op I) (p : ‖A‖ ≤ 1) (q : ‖B‖ ≤ 1) :
    ‖dg (A*X*B)‖ ≤ entryBudget X := by
  have he : ‖star B‖=‖B‖ := norm_star _
  nth_rw 1 [←star_star B]; refine (extensiveDG ..).trans ?_
  rw [he]; exact mul_le_of_le_one_right (entryBudget_ge _) ((mul_le_mul p q (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

lemma rotatedBound [Nonempty I] (A B X : Op I) (U : UNI I) (p : ‖A‖≤1) (q : ‖B‖≤1) :
    ‖dg (A*(twist U X)*B)‖ ≤ entryBudget X := by
  rw [twist_formula,←mul_assoc,←mul_assoc]
  rw [show A*U.val*X*star U.val*B=A*U.val*X*(star U.val*B) by simp [mul_assoc]]
  have he : ‖U.val‖=1 := CStarRing.norm_of_mem_unitary U.property
  refine extensiveDG' (A*U.val) (star U.val*B) X ((norm_mul_le ..).trans ?_) ((norm_mul_le ..).trans ?_)
  · rw [he,mul_one]; exact p
  rw [norm_star,he,one_mul]; exact q
end YM.CF.Window

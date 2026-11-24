import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # Positive finite matrix helpers -/
set_option autoImplicit false
noncomputable section

namespace YM.Six
open Matrix Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] {A B : Matrix n n ℂ}

/-- Finite positive definite ⇒ gap. -/
lemma gap_of_posDef (h : A.PosDef) : ∃ d : ℝ, 0 < d ∧ d • (1 : Matrix n n ℂ) ≤ A := by
  have ha : IsSelfAdjoint A := h.isHermitian.isSelfAdjoint
  obtain ⟨d,hd,H⟩ := (CFC.exists_pos_algebraMap_le_iff ha).mpr
    (fun x hx => h.isStrictlyPositive.spectrum_pos hx)
  exact ⟨d,hd,by rwa [←Algebra.algebraMap_eq_smul_one]⟩

omit [Nonempty n] [Fintype n] in
lemma posDef_of_gap {d : ℝ} (hd : 0 < d) (h : d • (1 : Matrix n n ℂ) ≤ A) : A.PosDef := by
  simpa using ((Matrix.PosDef.one).smul hd).add_posSemidef (Matrix.le_iff.mp h)

lemma hermitian_norm_bound (ha : A.IsHermitian) {r : ℝ} (h : ‖A‖ ≤ r) :
    A ≤ r • (1 : Matrix n n ℂ) := by
  rw [← Algebra.algebraMap_eq_smul_one]
  exact le_algebraMap_of_spectrum_le (fun x hx => calc
    x ≤ ‖x‖ := Real.le_norm_self x
    _ ≤ ‖A‖ := spectrum.norm_le_norm_of_mem hx
    _ ≤ r := h) ha.isSelfAdjoint

lemma stable_gap {a b : ℝ} (hg : a • (1 : Matrix n n ℂ) ≤ A)
    (hh : (A-B).IsHermitian) (he : ‖A-B‖ ≤ a-b) : b • (1 : Matrix n n ℂ) ≤ B := by
  have he := hermitian_norm_bound hh he
  rw [sub_smul] at he
  calc
    _ ≤ b • (1 : Matrix n n ℂ) + (A-a•1) := le_add_of_nonneg_right (sub_nonneg.mpr hg)
    _ = A - (a•1-b•1) := by abel
    _ ≤ A - (A-B) := sub_le_sub_left he _
    _ = B := sub_sub_cancel ..

lemma eventually_gap {ι : Type*} {M : ι → Matrix n n ℂ} {l : Filter ι} (hA : A.PosDef)
    (lim : Tendsto M l (𝓝 A)) (hh : ∀ᶠ i in l, (M i).IsHermitian) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ i in l, d • (1 : Matrix n n ℂ) ≤ M i := by
  obtain ⟨a,ha,hg⟩ := gap_of_posDef hA
  refine ⟨a/2,half_pos ha,?_⟩
  filter_upwards [Metric.tendsto_nhds.mp lim (a-a/2) (sub_pos.mpr (half_lt_self ha)),hh] with i h1 h2
  exact stable_gap hg (hA.isHermitian.sub h2) (by rw [←dist_eq_norm_sub,dist_comm] ; exact h1.le)

omit [Nonempty n] [DecidableEq n] in
lemma gram_mono {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ E] [InnerProductSpace ℂ F] (x : n → E) (y : n → F)
    (h : ∀ c : n → ℂ, ‖∑ i, c i • x i‖^2 ≤ ‖∑ i, c i • y i‖^2) :
    gram ℂ x ≤ gram ℂ y := by
  refine Matrix.le_iff.mpr (.of_dotProduct_mulVec_nonneg
    ((isHermitian_gram ℂ y).sub (isHermitian_gram ℂ x)) fun c => ?_)
  rw [Matrix.sub_mulVec,dotProduct_sub,star_dotProduct_gram_mulVec,star_dotProduct_gram_mulVec,
    sub_nonneg,inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K]
  exact_mod_cast h c

end YM.Six

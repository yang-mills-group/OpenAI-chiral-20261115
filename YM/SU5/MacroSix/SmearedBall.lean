import YM.SU5.MacroSix.UniformBall
import YM.SU5.MacroSix.SmearedSector

/-! # Preserve the full spectral Gram test after applying smeared fields in this sector -/
set_option autoImplicit false
noncomputable section
namespace YM.MacroSix
open Filter Function Finset Metric MeasureTheory Matrix Complex
open scoped Topology NNReal ENNReal InnerProductSpace MatrixOrder ComplexOrder BigOperators
open Cheer.MatrixZoom Projections Mink OS OS.Semigroup.Balloon ClockTest

variable (H : Hilbert) {J : Type*} [Fintype J] [DecidableEq J]

lemma unglue (v : J → H) (d : ℝ) (h : (d:ℂ) • (1 : Matrix J J ℂ) ≤ Matrix.gram ℂ v)
    (a : J → ℂ) : d * (∑ j, ‖a j‖^2) ≤ ‖coeffSum H v a‖^2 := by
  have he := ((Matrix.le_iff).mp h).dotProduct_mulVec_nonneg a
  have hb : star a ⬝ᵥ a = ↑(∑ j, ‖a j‖^2) := by
    simp [dotProduct, Complex.conj_mul']
  rw [sub_mulVec,dotProduct_sub, star_dotProduct_gram_mulVec, smul_mulVec, one_mulVec,
    dotProduct_smul, inner_self_eq_norm_sq_to_K, smul_eq_mul, sub_nonneg, hb, ← Complex.ofReal_mul] at he
  change ((d*(∑ j, ‖a j‖^2):ℝ):ℂ) ≤ (↑(‖coeffSum H v a‖):ℂ)^2 at he
  rw [← Complex.ofReal_pow] at he
  exact_mod_cast he

lemma gram_separates (v : J → H) (d : ℝ) (p : 0 < d)
    (h : (d:ℂ) • (1 : Matrix J J ℂ) ≤ Matrix.gram ℂ v) {a : J → ℂ} (u : a ≠ 0) :
    coeffSum H v a ≠ 0 := by
  let x := (EuclideanSpace.equiv J ℂ).symm a
  have hx : x ≠ 0 := EmbeddingLike.map_ne_zero_iff.mpr u
  have he : 0 < ∑ j, ‖a j‖^2 := lt_of_lt_of_eq (sq_pos_of_pos (norm_pos_iff.mpr hx)) x.norm_sq_eq
  intro hr; have ht := (mul_pos p he).trans_le (unglue H v d h a); simp [hr] at ht

lemma gram_positive (v : J → H) (d : ℝ) (p : 0 < d)
    (h : (d:ℂ) • (1 : Matrix J J ℂ) ≤ Matrix.gram ℂ v) : (Matrix.gram ℂ v).PosDef := by
  rw [Matrix.posDef_gram_iff_linearIndependent,Fintype.linearIndependent_iff]
  intro x he
  by_cases hg : x=0
  · simp [hg]
  exact (gram_separates H v d p h hg he).elim

lemma gram_price (v : J → H) (p : ∀ a : J → ℂ, a ≠ 0 → coeffSum H v a≠0) :
    ∃ d : ℝ, 0 < d ∧ (d:ℂ) • (1 : Matrix J J ℂ) ≤ Matrix.gram ℂ v := by
  let E := EuclideanSpace.equiv J ℂ
  let T := (coeffSum H v).comp E.toLinearEquiv.toLinearMap
  have hc : Continuous fun x ↦ ‖T x‖^2 := (T.continuous_of_finiteDimensional.norm).pow _
  obtain ⟨d,h,w⟩ := eventualSpherePrice (fun _ : ℕ ↦ T) (fun ι _ x q U hv ↦ by
    let m := ‖T x‖^2
    have hm : 0 < m := sq_pos_of_pos (norm_pos_iff.mpr (p (E x) (EmbeddingLike.map_ne_zero_iff.mpr q)))
    exact ⟨m/2,half_pos hm,(hc.continuousAt.tendsto.comp hv).eventually (lt_mem_nhds (half_lt_self hm))⟩)
  obtain ⟨-,H'⟩ := w.exists
  exact ⟨d,h,priceInOrder v d (scalarOfCoeff v d H')⟩

lemma gram_shadow (v : J → H) (P : Spectral.PVM H E4) (A : Set E4) (e : MeasurableSet A)
    (d : ℝ) (h : (d:ℂ) • (1 : Matrix J J ℂ) ≤ Matrix.gram ℂ (fun j ↦ P.region A (v j))) :
    (d:ℂ) • (1 : Matrix J J ℂ) ≤ Matrix.gram ℂ v := by
  refine priceInOrder v d ?_
  intro a
  have he := unglue H _ d h a
  rw [coeffSum_projection] at he
  exact he.trans (norm_sq_grant P e (coeffSum H v a))

lemma ball_stable (S : OS.Semigroup H timeAxis) (u v : J → H) (r : ℝ≥0) (hr : 0 < r)
    (f : Full → ℝ) (p : SmoothDensity f) (e : ∀ j, u j=reachVector S r f (v j))
    (A : Set E4) (h : MeasurableSet A)
    (hy : ∀ x : H, ∀ᵐ y ∂(S.ℚmeasure.diagonal x).restrict A, jointCost r f y≠0)
    (d : ℝ) (hp : 0 < d)
    (hx : (d:ℂ) • (1 : Matrix J J ℂ) ≤ Matrix.gram ℂ (fun j ↦ S.ℚmeasure.region A (v j))) :
    ∃ t : ℝ, 0 < t ∧ (t:ℂ) • (1 : Matrix J J ℂ) ≤ Matrix.gram ℂ (fun j ↦ S.ℚmeasure.region A (u j)) ∧
      (t:ℂ) • (1 : Matrix J J ℂ) ≤ Matrix.gram ℂ u := by
  let K := S.ℚmeasure.region A
  obtain ⟨t,h₁,h₂⟩ := gram_price H (fun j ↦ K (u j)) (fun a q ↦ by
    have he : K (coeffSum H v a) ≠ 0 := by
      rw [← coeffSum_projection H K v a]
      exact gram_separates H _ d hp hx q
    rw [coeffSum_projection]
    rw [coeffSum_apply]; simp_rw [e]; rw [← reach_sum S _ r f v a p]
    exact window_detects S h (coeffSum H v a) r f p (hy _) he)
  exact ⟨t,h₁,h₂, gram_shadow H u _ A h _ h₂⟩
end YM.MacroSix
#print axioms YM.MacroSix.ball_stable

import YM.SU5.MacroSix.PolarizedMeasure
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Order

/-! # Uniform lower matrix price (the ball grant in `l:zoommat`)

Argue with compactness of the coefficient unit sphere, not one choice of coefficients
before an eventual threshold. The conclusion is in Mathlib's positive semidefinite order.
Open window prices (at every nonempty relatively indicated region); no boundary-zero
hypothesis needed.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Cheer.MatrixZoom

open Function Finset Set Filter MeasureTheory Matrix Complex Metric
open scoped Topology MatrixOrder ComplexOrder BigOperators NNReal ENNReal InnerProductSpace

variable {J : Type*} [Fintype J] {H : Hilbert}

-- also useful for fixed-smear Gram grant later
lemma spherePrice (T : EuclideanSpace ℂ J →ₗ[ℂ] H) (d : ℝ)
    (h : ∀ x, ‖x‖=1 → d ≤ ‖T x‖^2) : ∀ x, d * ‖x‖^2 ≤ ‖T x‖^2 := by
  intro x
  by_cases p : x=0
  · simp [p]
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr p
  let c := (‖x‖:ℂ)
  have hc : ‖c‖ = ‖x‖ := by simp [c]
  let y := c⁻¹ • x
  have hy : ‖y‖=1 := by rw [show ‖y‖ = ‖c⁻¹‖*‖x‖ from norm_smul .., norm_inv, hc]; exact inv_mul_cancel₀ hp.ne'
  have he : c • y = x := smul_inv_smul₀ (norm_ne_zero_iff.mp (hc ▸ hp.ne')) _
  calc _ ≤ ‖x‖^2 * ‖T y‖^2 := by rw [mul_comm d]; gcongr; exact h y hy
       _ = ‖T x‖^2 := by rw [← hc, ← mul_pow, ← norm_smul, ← T.map_smul, he]

lemma eventualSpherePrice (T : ℕ → EuclideanSpace ℂ J →ₗ[ℂ] H)
    (h : ∀ (ι : ℕ → ℕ) (_ : Tendsto ι atTop atTop) (x : EuclideanSpace ℂ J) (_ : x ≠ 0)
      (u : ℕ → EuclideanSpace ℂ J) (_ : Tendsto u atTop (𝓝 x)),
        ∃ t : ℝ, 0 < t ∧ ∀ᶠ i in atTop, t < ‖T (ι i) (u i)‖^2) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ i in atTop, ∀ x : EuclideanSpace ℂ J, d * ‖x‖^2 ≤ ‖T i x‖^2 := by
  classical
  by_contra! H₀
  let e (i : ℕ) := (1/2:ℝ)^i
  have he : ∀ i : ℕ, ∃ n ≥ i, ∃ x : EuclideanSpace ℂ J, ‖x‖=1 ∧ ‖T n x‖^2 < e i := by
    intro i
    obtain ⟨n,w,y,p⟩ := frequently_atTop.mp (H₀ (e i) (by dsimp [e]; positivity)) i
    refine ⟨n,w,?_⟩
    by_contra! hn
    exact p.not_ge (spherePrice (T n) (e i) hn y)
  choose ι hi u hu hx using he
  have hK : ∀ i, u i ∈ Metric.sphere 0 1 := fun i ↦ mem_sphere.mpr ((dist_zero_right _).trans (hu i))
  obtain ⟨x,w,l,H,Hl⟩ := (isCompact_sphere _ _).tendsto_subseq hK
  have hv := H.tendsto_atTop
  have hp : x ≠ 0 := fun p ↦ by simp [p] at w
  obtain ⟨c,q,v⟩ := h (ι ∘ l) ((tendsto_atTop_mono hi tendsto_id).comp hv) x hp _ Hl
  have hh : Tendsto (e ∘ l) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp hv
  obtain ⟨i,t,y⟩ := (v.and (hh.eventually (gt_mem_nhds q))).exists
  exact lt_asymm (hx (l i)) (lt_trans y t)

lemma scalarOfCoeff {H : Hilbert} (v : J → H) (d : ℝ)
    (h : ∀ x : EuclideanSpace ℂ J, d * ‖x‖^2 ≤ ‖coeffSum H v (EuclideanSpace.equiv J ℂ x)‖^2)
    (a : J → ℂ) : d * (∑ j, ‖a j‖^2) ≤ ‖∑ j, a j • v j‖^2 := by
  let E := EuclideanSpace.equiv J ℂ
  let x := E.symm a
  have hx := h x
  rw [x.norm_sq_eq] at hx
  exact hx -- E is identity on coordinates.

lemma priceInOrder [DecidableEq J] (v : J → H) (d : ℝ)
    (h : ∀ a : J → ℂ, d * (∑ j, ‖a j‖^2) ≤ ‖∑ j, a j • v j‖^2) :
    (d:ℂ) • (1 : Matrix J J ℂ) ≤ Matrix.gram ℂ v := by
  apply Matrix.le_iff.mpr
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (Matrix.isHermitian_gram ℂ v).sub
      (Matrix.isHermitian_one.smul (show IsSelfAdjoint (d:ℂ) by simp [IsSelfAdjoint]))
  intro a
  rw [sub_mulVec,dotProduct_sub, star_dotProduct_gram_mulVec, smul_mulVec, one_mulVec,
    dotProduct_smul, inner_self_eq_norm_sq_to_K, smul_eq_mul]
  rw [sub_nonneg]
  have he : star a ⬝ᵥ a = ↑(∑ j, ‖a j‖^2) := by
    simp [dotProduct, Complex.conj_mul']
  rw [he, ← Complex.ofReal_mul]
  change ((d*(∑ j, ‖a j‖^2):ℝ):ℂ) ≤ ((‖∑ i, a i • v i‖:ℝ):ℂ)^2
  rw [← Complex.ofReal_pow]
  exact_mod_cast h a

lemma coeffSum_projection (H : Hilbert) (R : H.Op) (v : J → H) (a : J → ℂ) :
    coeffSum H (fun j ↦ R (v j)) a = R (coeffSum H v a) := by
  simp only [coeffSum_apply,_root_.map_sum,map_smul]

local notation "M" => Measure E4

/-- Lyrical convergence along subsequences of *every* convergent ray of coefficients implies
a uniform price for any qualifying spectral window (after rescaling). -/
lemma combinationBall (S : OS.Semigroup H timeAxis) (ρ : ℕ → ℝ) (v : ℕ → J → H)
    (μ : J → Narrow) (h : ∀ (ι : ℕ → ℕ), Tendsto ι atTop atTop →
      ∀ a : J → ℂ, ∀ A : ℕ → J → ℂ, (∀ j, Tendsto (fun i ↦ A i j) atTop (𝓝 (a j))) →
        Lyrical (combinationLaw μ a) (fun i ↦ outlay S (coeffSum H (v (ι i)) (A i)) (ρ (ι i))))
    (D : Set E4) (hd : IsOpen D) (hw : ∀ j, 0 < (μ j : M) D) [DecidableEq J] :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ i in atTop,
      let u j := S.ℚmeasure.region (press (ρ i) D) (v i j)
      (d:ℂ) • (1 : Matrix J J ℂ) ≤ Matrix.gram ℂ u := by
  let R i := S.ℚmeasure.region (press (ρ i) D)
  let E := EuclideanSpace.equiv J ℂ
  let u i (j : J) := R i (v i j)
  let T i := (coeffSum H (u i)).comp E.toLinearEquiv.toLinearMap
  have HH (ι : ℕ → ℕ) (hi : Tendsto ι atTop atTop) (x : EuclideanSpace ℂ J) (hx : x ≠ 0)
      (U : ℕ → EuclideanSpace ℂ J) (hU : Tendsto U atTop (𝓝 x)) :
      ∃ d : ℝ, 0 < d ∧ ∀ᶠ i in atTop, d < ‖T (ι i) (U i)‖^2 := by
    let X := combinationLaw μ (E x)
    let A i := E (U i)
    let f i := v (ι i)
    have hw : 0 < (X:M) D := combinationLaw_pos μ _ (show E x ≠ 0 from EmbeddingLike.map_ne_zero_iff.mpr hx) D hw
    let m := (X:M).real D
    have hp : 0 < m := ENNReal.toReal_pos hw.ne' (measure_ne_top _ _)
    refine ⟨m/2, half_pos hp, ?_⟩
    apply Eventually.mono (knock (m/2) D (h ι hi (E x) A (tendsto_pi_nhds.mp
      (E.continuous.continuousAt.tendsto.comp hU)))
      (fun p ↦ by rw [p] at hw; simp at hw) hd (half_lt_self hp))
    intro i w
    exact w.trans_eq ((norm_region S (coeffSum H (f i) (A i)) (ρ (ι i)) D hd.measurableSet).symm.trans
      (congrArg (fun v : H ↦ ‖v‖^2) (coeffSum_projection H (R (ι i)) (f i) (A i)).symm))
  obtain ⟨d,p,w⟩ := eventualSpherePrice T HH
  exact ⟨d,p,w.mono fun i h ↦ priceInOrder (u i) d (scalarOfCoeff (u i) d h)⟩

omit [Fintype J] in
/-- The matrix used in `combinationBall` is the actual restriction of spectral cross-prices. -/
lemma gram_press [DecidableEq J] (S : OS.Semigroup H timeAxis) (ρ : ℝ) (v : J → H)
    (D : Set E4) (hd : MeasurableSet D) :
    (Matrix.of fun j k ↦ crossIntegral S.ℚmeasure (v j) (v k)
      ((press ρ D).indicator fun _ ↦ (1:ℂ))) =
        Matrix.gram ℂ (fun j ↦ S.ℚmeasure.region (press ρ D) (v j)) := by
  let A := S.ℚmeasure
  let X := press ρ D
  have he := pressured ρ hd
  ext1 j k
  simp only [Matrix.of_apply, Matrix.gram_apply, crossIntegral_indicator _ _ _ he]
  have hp (x y : H) : inner ℂ (A.region X x) y = inner ℂ x (A.region X y) := by
    nth_rw 1 [← A.real he]; rw [ContinuousLinearMap.adjoint_inner_left]
  rw [show inner ℂ (S.ℚmeasure.region _ _) (S.ℚmeasure.region _ _) =
      inner ℂ (v j) (A.region X (A.region X (v k))) from hp _ _]
  rw [A.idempotent he]

end YM.Cheer.MatrixZoom
#print axioms YM.Cheer.MatrixZoom.combinationBall

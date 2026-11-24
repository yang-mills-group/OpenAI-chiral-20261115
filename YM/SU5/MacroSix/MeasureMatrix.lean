import YM.SU5.Cheer.Pavilion

/-! # From rescaled matrix kernel to spectral measure convergence

Standalone analytic part. Take *every* diagonal of the matrix-valued measure (any
complex vector of coefficients). In fact the weak convergence estimate tolerates
varying/tending coefficients -- this is one useful route to a uniform open-ball grant.
The criterion we use on each combination is the project's already verified upgrade of
Fourier-Laplace costs (`Lyrical.march`). This way there is no topology on vector
measures needed. Subsequent file will also spell out the explicit off-diagonal version
(polarizations), including on compact-uniformly-moving tests.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Cheer.MatrixZoom

open Filter MeasureTheory Measure Mink Function Finset
open scoped Topology NNReal ENNReal InnerProductSpace BigOperators

variable {J : Type*} [Fintype J]

def combinationLaw (μ : J → Narrow) (a : J → ℂ) : Narrow := ∑ j, ‖a j‖₊^2 • μ j

lemma combinationLaw_bright (μ : J → Narrow) (h : ∀ j, Brilliant (μ j)) (a : J → ℂ) :
    Brilliant (combinationLaw μ a) := by
  unfold Brilliant combinationLaw
  rw [FiniteMeasure.toMeasure_sum, ae_finsetSum_measure_iff]
  exact fun j _ ↦ Measure.ae_smul_measure (h j) _

lemma combinationLaw_integral (μ : J → Narrow) (a : J → ℂ) (f : E4 → ℂ)
    (h : ∀ j, Integrable f (μ j : Measure E4)) :
    (∫ v, f v ∂(combinationLaw μ a : Measure E4)) =
      ∑ j, star (a j) * a j * ∫ v, f v ∂(μ j : Measure E4) := by
  unfold combinationLaw
  simp only [FiniteMeasure.toMeasure_sum, FiniteMeasure.toMeasure_smul]
  rw [integral_finsetSum_measure (fun j _ ↦ (h j).smul_measure_nnreal)]
  simp [integral_smul_nnreal_measure, NNReal.smul_def,
    Complex.real_smul, Complex.conj_mul']

lemma combinationLaw_flap (μ : J → Narrow) (h : ∀ j, Brilliant (μ j))
    (a : J → ℂ) (p : Space3) (w : ℂ) (hw : 0 ≤ w.re) :
    FLap (combinationLaw μ a) p w = ∑ j, star (a j) * a j * FLap (μ j) p w :=
  combinationLaw_integral μ a (tendsK p w) fun j ↦ destined _ p w (h j) hw

lemma combinationLaw_pos (μ : J → Narrow) (a : J → ℂ) (ha : a ≠ 0)
    (D : Set E4) (hd : ∀ j, 0 < (μ j : Measure E4) D) :
    0 < (combinationLaw μ a : Measure E4) D := by
  classical
  have he : ∃ j, a j ≠ 0 := not_forall.mp (fun h ↦ ha (funext h))
  obtain ⟨j,hj⟩ := he
  simp only [combinationLaw, FiniteMeasure.toMeasure_sum, FiniteMeasure.toMeasure_smul,
    Measure.finsetSum_apply]
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun i (_ : i ∈ (univ : Finset J)) ↦
    (zero_le (a := (‖a i‖₊^2 • (μ i : Measure E4)) D))) (mem_univ j))
  change 0 < (((‖a j‖₊^2 : ℝ≥0) : ℝ≥0∞) • (μ j : Measure E4)) D
  simp only [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_pos (by simp [hj]) (hd j).ne'

lemma pairing_expansion (H : Hilbert) (T : H.Op) (u v : J → H) (a b : J → ℂ) :
    inner ℂ (∑ j, a j • u j) (T (∑ j, b j • v j)) =
      ∑ j, ∑ k, star (a j) * b k * inner ℂ (u j) (T (v k)) := by
  rw [sum_inner]
  simp only [_root_.map_sum, _root_.map_smul, inner_sum, inner_smul_left, inner_smul_right, mul_assoc]
  exact sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ mul_left_comm (b k) (star (a j)) (inner ℂ (u j) (T (v k)))

/-- All superpositions of a finite matrix family. No spectral test vector is
inferred from entry-wise scalar diagonals alone; `p` is a *full matrix* input. -/
theorem combinationLaw_lyrical (H : Hilbert) (S : OS.Semigroup H timeAxis)
    (ρ : ℕ → ℝ≥0) (v : ℕ → J → H) (μ : J → Narrow) (h : ∀ j, Brilliant (μ j))
    [DecidableEq J]
    (p : ∀ (j k : J) (x : Space3) (t : ℝ≥0), Tendsto (fun i ↦
      inner ℂ (v i j) (S.U ((ρ i:ℝ) • shore x) (S.E (ρ i*t) (v i k)))) atTop
      (𝓝 (if j=k then FLap (μ j) x ↑(t:ℝ) else 0)))
    {ι : ℕ → ℕ} (hi : Tendsto ι atTop atTop)
    {A : ℕ → J → ℂ} {a : J → ℂ} (ha : ∀ j, Tendsto (fun i ↦ A i j) atTop (𝓝 (a j))) :
    Lyrical (combinationLaw μ a)
      (fun i ↦ outlay S (∑ j, A i j • v (ι i) j) ↑(ρ (ι i))) := by
  refine ⟨fun i ↦ radiant _ _ _ (ρ _).property, combinationLaw_bright μ h a, fun x t ↦ ?_⟩
  let T (i : ℕ) := (S.U ((ρ (ι i):ℝ) • shore x)).comp (S.E (ρ (ι i)*t))
  let f (i : ℕ) (j k : J) := inner ℂ (v (ι i) j) (T i (v (ι i) k))
  let g (j : J) := FLap (μ j) x ↑(t:ℝ)
  have hf (j k : J) : Tendsto (fun i ↦ f i j k) atTop (𝓝 (if j=k then g j else 0)) :=
    (p j k x t).comp hi
  have he (j : J) : Tendsto (fun i ↦ ∑ k, star (A i j) * A i k * f i j k)
      atTop (𝓝 (star (a j) * a j * g j)) := by
    have ht : Tendsto (fun i ↦ ∑ k, star (A i j) * A i k * f i j k) atTop
        (𝓝 (∑ k, star (a j) * a k * (if j=k then g j else 0))) :=
      tendsto_finsetSum _ fun k _ ↦ ((ha j).star.mul (ha k)).mul (hf j k)
    simpa [mul_ite] using ht
  rw [combinationLaw_flap _ h a x _ t.property]
  simp_rw [back]
  change Tendsto (fun i ↦ inner ℂ (∑ j, A i j • v (ι i) j) (T i (∑ j, A i j • v (ι i) j)))
    atTop (𝓝 (∑ j, star (a j) * a j * g j))
  simp_rw [pairing_expansion]
  exact tendsto_finsetSum _ fun j _ ↦ he j

/-- `march` with no hypothesis of nonzero total. -/
lemma weak {F : ℕ → Narrow} {μ : Narrow} (h : Lyrical μ F) : Tendsto F atTop (𝓝 μ) := by
  by_cases H : μ=0
  · subst μ
    apply FiniteMeasure.tendsto_zero_of_tendsto_zero_mass
    exact tendsto_subtype_rng.mpr h.massR
  exact h.march fun v ↦ H (FiniteMeasure.toMeasure_injective v)

end YM.Cheer.MatrixZoom
#print axioms YM.Cheer.MatrixZoom.combinationLaw_lyrical

import YM.SU5.MacroSix.MovingMeasure

/-! # Polarized measure estimates

We represent integration against a *finite complex off-diagonal spectral measure* in Lean
by polarization (explicit fixed combination of four integrals against finite, **positive**
measures). We also certify the PVM value on any Borel set to fix the identification.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Cheer.MatrixZoom

open Filter Function Finset MeasureTheory Complex
open scoped Topology NNReal ENNReal InnerProductSpace BigOperators

variable {H : Hilbert}

def polar {W : Type*} [AddCommGroup W] [SMul ℂ W] (Q : W → ℂ) (x y : W) : ℂ :=
  (Q (x+y) - Q (x-y) - I*(Q (x + I • y)-Q (x - I • y)))/4

def crossIntegral {Ω : Type*} [MeasurableSpace Ω] (P : Spectral.PVM H Ω)
    (x y : H) (f : Ω → ℂ) : ℂ := polar (fun v : H ↦ ∫ w, f w ∂P.diagonal v) x y

lemma polar_inner (H : Hilbert) (T : H.Op) (x y : H) :
    polar (fun v : H ↦ inner ℂ v (T v)) x y = inner ℂ x (T y) := by
  simp only [polar,map_add,map_sub,map_smul,inner_add_left,inner_add_right,inner_sub_left,
    inner_sub_right,inner_smul_left,inner_smul_right,conj_I]; ring_nf; simp; ring

lemma polar_comp (H : Hilbert) {W : Type*} [AddCommGroup W] [Module ℂ W]
    (Q : H → ℂ) (T : W →ₗ[ℂ] H) (x y : W) :
    polar (fun v ↦ Q (T v)) x y = polar Q (T x) (T y) := by
  simp [polar]

lemma crossIntegral_indicator {Ω : Type*} [MeasurableSpace Ω] (P : Spectral.PVM H Ω)
    (x y : H) {D : Set Ω} (hd : MeasurableSet D) :
    crossIntegral P x y (D.indicator fun _ ↦ (1:ℂ)) = inner ℂ x (P.region D y) := by
  have he (v : H) : ↑((P.diagonal v).real D) = inner ℂ v (P.region D v) := P.at_pair hd v
  unfold crossIntegral
  simp_rw [integral_indicator hd, setIntegral_const, Complex.real_smul, mul_one, he]
  exact polar_inner H (P.region D) x y

lemma sumPolar {J : Type*} (s : Finset J) {V : Type*} [AddCommGroup V] [SMul ℂ V]
    (v w : V) (Q : J → V → ℂ) :
    polar (fun x ↦ ∑ j ∈ s, Q j x) v w = ∑ j ∈ s, polar (Q j) v w := by
  simp only [polar, sum_div, mul_sum, ← sum_sub_distrib]

lemma tendstoPolar {W : Type*} [AddCommGroup W] [SMul ℂ W] (v w : W)
    (Q : ℕ → W → ℂ) (K : W → ℂ) (h : ∀ x, Tendsto (fun i ↦ Q i x) atTop (𝓝 (K x))) :
    Tendsto (fun i ↦ polar (Q i) v w) atTop (𝓝 (polar K v w)) := by
  exact (((h (v+w)).sub (h (v-w))).sub (((h (v+I • w)).sub
    (h (v-I • w))).const_mul I)).div_const _

variable {J : Type*} [Fintype J]
local notation "M" => Measure E4

/-- Reusable map bundling coefficients, plain `J → ℂ` to Hilbert. No inner product
on the coefficient type implicit. -/
def coeffSum (H : Hilbert) (v : J → H) : (J → ℂ) →ₗ[ℂ] H where
  toFun a := ∑ j, a j • v j
  map_add' := by intro x y; simp [add_smul,Finset.sum_add_distrib]
  map_smul' := by intro a x; simp [smul_sum,smul_smul]

lemma coeffSum_apply (H : Hilbert) (v : J → H) (a : J → ℂ) :
    coeffSum H v a = ∑ j, a j • v j := rfl

lemma coeffSum_single [DecidableEq J] (H : Hilbert) (v : J → H) (j : J) :
    coeffSum H v (Pi.single j 1) = v j := by
  rw [coeffSum_apply]
  classical
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ h; simp [Pi.single_eq_of_ne h]
  simp

lemma combinationCross (μ : J → Narrow) (f : E4 → ℂ)
    (h : ∀ j, Integrable f (μ j : Measure E4)) (a b : J → ℂ) :
    polar (fun a' ↦ ∫ x, f x ∂(combinationLaw μ a' : Measure E4)) a b =
      ∑ j, star (a j) * b j * ∫ v, f v ∂(μ j : Measure E4) := by
  simp_rw [combinationLaw_integral _ _ f h, sumPolar]
  refine sum_congr rfl fun j _ ↦ ?_
  simp only [polar, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, star_add, star_sub,
    star_mul, Complex.star_def, conj_I]
  ring_nf; simp; ring

lemma crossLimit (S : OS.Semigroup H timeAxis)
    (ρ : ℕ → ℝ≥0) (v : ℕ → J → H) (μ : J → Narrow) (h : ∀ j, Brilliant (μ j))
    (g : ∀ a : J → ℂ,
      Tendsto (fun i ↦ outlay S (coeffSum H (v i) a) (ρ i:ℝ)) atTop (𝓝 (combinationLaw μ a)))
    (a b : J → ℂ) {F : ℕ → E4 → ℂ} {f : E4 → ℂ} (X : ZoomTest F f) :
    Tendsto (fun i ↦ crossIntegral S.ℚmeasure (coeffSum H (v i) a) (coeffSum H (v i) b)
      (fun p ↦ F i ((ρ i:ℝ) • p))) atTop (𝓝 (∑ j, star (a j) * b j * ∫ x, f x ∂(μ j:M))) := by
  let Q (i : ℕ) (w : H) := ∫ p, F i ((ρ i:ℝ) • p) ∂S.ℚmeasure.diagonal w
  let K (a : J → ℂ) := ∫ x, f x ∂(combinationLaw μ a:M)
  have he (w : J → ℂ) : Tendsto (fun i ↦ Q i (coeffSum H (v i) w)) atTop (𝓝 (K w)) := by
    let D (i : ℕ) := coeffSum H (v i) w
    let U i := outlay S (D i) (ρ i:ℝ)
    have hu (i : ℕ) : Brilliant (U i) := radiant S (D i) _ (ρ i).property
    refine (zoomTestLimit (g w) hu (combinationLaw_bright μ h w) X).congr fun i ↦ ?_
    exact integral_map (eligible (ρ i:ℝ) |>.measurable.aemeasurable)
      (X.each (hu i) i).aestronglyMeasurable
  rw [← combinationCross μ f (fun j ↦ X.target (h j)) a b]
  exact (tendstoPolar a b (fun i w ↦ Q i (coeffSum H (v i) w)) K he).congr
    fun i ↦ polar_comp H (Q i) (coeffSum H (v i)) a b

lemma entryLimit [DecidableEq J] (S : OS.Semigroup H timeAxis)
    (ρ : ℕ → ℝ≥0) (v : ℕ → J → H) (μ : J → Narrow) (h : ∀ j, Brilliant (μ j))
    (g : ∀ a : J → ℂ,
      Tendsto (fun i ↦ outlay S (coeffSum H (v i) a) (ρ i:ℝ)) atTop (𝓝 (combinationLaw μ a)))
    (j k : J) {F : ℕ → E4 → ℂ} {f : E4 → ℂ} (X : ZoomTest F f) :
    Tendsto (fun i ↦ crossIntegral S.ℚmeasure (v i j) (v i k)
      (fun p ↦ F i ((ρ i:ℝ) • p))) atTop (𝓝 (if j=k then ∫ x, f x ∂(μ j:M) else 0)) := by
  have hp := crossLimit S ρ v μ h g (Pi.single j 1) (Pi.single k 1) X
  simp_rw [coeffSum_single] at hp
  rw [Finset.sum_eq_single j] at hp
  · rw [Pi.single_eq_same] at hp
    by_cases e : j=k
    · subst k; simpa using hp
    simpa [Pi.single_eq_of_ne e,e] using hp
  · intro i _ e; simp [Pi.single_eq_of_ne e]
  simp

end YM.Cheer.MatrixZoom
#print axioms YM.Cheer.MatrixZoom.combinationCross
#print axioms YM.Cheer.MatrixZoom.entryLimit

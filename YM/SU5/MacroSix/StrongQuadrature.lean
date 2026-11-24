import YM.SU5.MacroSix.ContinuityAverage
/-! Hilbert-valued costs for the continuous projections in the six-clan theorem. Use
local instances to keep *all* the rest of the structure (the ℂ Hilbert of the Spinor/Card
construction), without dependence on choices of `NormedSpace ℝ` instances exposed later. -/
set_option autoImplicit false
noncomputable section
namespace YM.MacroSix
open Filter MeasureTheory Function Finset
open scoped Topology Matrix MatrixOrder BigOperators ComplexOrder InnerProductSpace NNReal ENNReal
open YM.CF.Buffered.Afterglow.Tower.Aria

def total {X : Type*} [MeasurableSpace X] (H : Hilbert) (μ : Measure X) (f : X → H) : H := by
  letI := NormedSpace.restrictScalars ℝ ℂ H.space
  exact ∫ x, f x ∂μ

section basic
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
  (H W : Hilbert) (f g : X → H) (v : H)

lemma total_inner_right (h : Integrable f μ) :
    inner ℂ v (total H μ f) = ∫ x, inner ℂ v (f x) ∂μ := by
  letI := NormedSpace.restrictScalars ℝ ℂ H.space
  letI : IsScalarTower ℝ ℂ H.space := RestrictScalars.isScalarTower ℝ ℂ H.space
  exact ((innerSL ℂ v).integral_comp_comm h).symm

lemma total_inner_left (h : Integrable f μ) :
    inner ℂ (total H μ f) v = ∫ x, inner ℂ (f x) v ∂μ := by
  rw [← inner_conj_symm (𝕜:=ℂ), total_inner_right μ H f v h, ← integral_conj]
  simp_rw [inner_conj_symm]

lemma total_pair (h : Integrable f μ) (hg : Integrable g μ) :
    inner ℂ (total H μ f) (total H μ g) = ∫ x, ∫ y, inner ℂ (f x) (g y) ∂μ ∂μ := by
  simp_rw [total_inner_left μ H f (total H μ g) h,total_inner_right μ H g _ hg]

lemma total_comp (T : H →L[ℂ] W) (h : Integrable f μ) :
    total W μ (T ∘ f) = T (total H μ f) := by
  letI := NormedSpace.restrictScalars ℝ ℂ H.space
  letI := NormedSpace.restrictScalars ℝ ℂ W.space
  letI : IsScalarTower ℝ ℂ H.space := RestrictScalars.isScalarTower ℝ ℂ H.space
  letI : IsScalarTower ℝ ℂ W.space := RestrictScalars.isScalarTower ℝ ℂ W.space
  exact T.integral_comp_comm h
end basic

open Grid

/-- Convenient all-orders interface for the previous abstract principle when the
projected action is supplied as a continuous extension on the second (sub-)Hilbert. -/
theorem transportSum_limit {I : Type*} [Fintype I] (G : Type*) [AddCommGroup G]
    (H F : Hilbert) (T : F →L[ℂ] H) (project : H →L[ℂ] F)
    (δ : ℕ → ℝ) (U : G → H.Op) (ρ : ℕ → (I → ℤ) → G) (α : G → I → ℝ)
    (p : Setup δ U ρ α) (V : (I → ℝ) → F.Op)
    (hV : ∀ (f : (I → ℝ) → F) (_ : Continuous f), Continuous fun x ↦ V x (f x))
    (h : ∀ i b x, U (ρ i b) (T x) = T (V (place (δ i) b) x))
    (D : ℕ → Mist G)
    (u : ∀ K ∈ 𝓝 (0 : I → ℝ), ∀ᶠ i in atTop, (D i).holds (fun g ↦ α g ∈ K))
    (v : ∀ x, Tendsto (fun i ↦ (D i).mean fun g ↦ U g x) atTop (𝓝 (T (project x))))
    (f : (I → ℝ) → H) (q : Continuous f) (w : HasCompactSupport f) :
    Tendsto (fun i ↦ transportSum δ U ρ f i) atTop
      (𝓝 (T (total F volume fun x ↦ V x (project (f x))))) := by
  letI := NormedSpace.restrictScalars ℝ ℂ H.space
  letI : IsScalarTower ℝ ℂ H.space := RestrictScalars.isScalarTower ℝ ℂ H.space
  let g (x : I → ℝ) := V x (project (f x))
  have he : Continuous g := hV (project ∘ f) (project.continuous.comp q)
  have hk : HasCompactSupport g := HasCompactSupport.of_support_subset_isCompact w fun x b ↦
    subset_tsupport f (show f x ≠ 0 from fun p ↦ b (by unfold g; rw [p, map_zero, map_zero]))
  rw [← show total H volume (T ∘ g) = _ from total_comp (μ:=volume) F H g T
    (he.integrable_of_hasCompactSupport hk)]
  exact p.limit (T.comp project) f q w D u v (T ∘ g) (T.continuous.comp he) (hk.comp_left (map_zero T))
    fun i k ↦ (h i k _).symm
end YM.MacroSix
#print axioms YM.MacroSix.transportSum_limit

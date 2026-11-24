/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.ParametricIntegral
/- adapted from YM/EveryPhase/Pages.lean. Variant: local bound known entire domain eventually μ-a.e. over COUNTABLE allocated circle and pointwise readings separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.DPress.Analytic
open Function Set Filter MeasureTheory Complex Metric
open scoped Topology NNReal ContDiff Classical
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedSpace ℂ E][IsScalarTower ℝ ℂ E] [CompleteSpace E]
theorem plumes {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {F : α → ℂ → E} {U : Set ℂ} {C : ℝ} (h : IsOpen U) (he : ∀ i, DifferentiableOn ℂ (F i) U)
    (ha : ∀ x∈U, Integrable (fun i => F i x) μ) (hb : ∀ x∈U,∀ᵐ i∂μ, ‖F i x‖≤C) :
    DifferentiableOn ℂ (fun x => ∫ i, F i x ∂μ) U := by
  intro x hx
  obtain ⟨r,hr,hU⟩ := Metric.mem_nhds_iff.mp (h.mem_nhds hx)
  have ht : 0<r/2 := by linarith
  let B := ball x (r/2)
  have hB : B ⊆ U := (ball_subset_ball (by linarith : r/2 ≤ r)).trans hU
  let D (z : ℂ) (i : α) := deriv (F i) z
  have hv i y (hy : y∈B) : HasDerivAt (F i) (D y i) y :=
    ((he i).differentiableAt (h.mem_nhds (hB hy))).hasDerivAt
  classical
  have H : ∀ᵐ i∂ μ, ∀ x∈U, ‖F i x‖≤C:=by
    letI : Nonempty U:=⟨x,hx⟩
    let X:=TopologicalSpace.denseSeq U -- tuning
    have H: ∀ᵐ i∂ μ,∀ j:ℕ,‖F i (X j)‖ ≤ C:= eventually_countable_forall.mpr (fun i=>hb _ (X i).property)
    filter_upwards [H] with i t y p
    have ht :Continuous (U.restrict (F i)):= continuousOn_iff_continuous_restrict.mp (he i).continuousOn
    exact closure_minimal (s:=range X) (by rintro v ⟨e,rfl⟩; exact t _) (isClosed_le ht.norm (continuous_const (y:=C))) (TopologicalSpace.denseRange_denseSeq U ⟨y,p⟩)
  have hp : ∀ᵐ i∂ μ, ∀ y ∈ B, ‖D y i‖ ≤ C/(r/2) := by
    filter_upwards [H] with i hfp y hy
    -- duplicate declaration? indent
    /- have hp i y (hy : y∈B) : ‖D y i‖ ≤ C/(r/2) := by -/
    have hw : closedBall y (r/2) ⊆ U := by
      intro w hw; exact hU (mem_ball.mpr ((dist_triangle w y x).trans_lt (by linarith [mem_closedBall.mp hw, mem_ball.mp hy])))
    dsimp only [D]; rw [← Complex.cderiv_eq_deriv h (he i) ht hw]; exact Complex.norm_cderiv_le ht
      fun w hw' => hfp w (hw (sphere_subset_closedBall hw'))
  classical
  have hm : AEStronglyMeasurable (D x) μ := by
    let G y (i : α) := if y∈U then slope (F i) x y else 0
    have hG (y) : AEStronglyMeasurable (G y) μ := by
      by_cases H : y∈U
      · simp only [G,H,if_true,slope_def_module]; exact ((ha y H).aestronglyMeasurable.sub
          (ha x hx).aestronglyMeasurable).const_smul (y-x)⁻¹
      simp only [G,H,if_false]; exact aestronglyMeasurable_const
    apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] x) hG
    refine ae_of_all _ fun i => ((hv i x (mem_ball_self ht)).tendsto_slope).congr'
      (Eventually.mono (show ∀ᶠ z in 𝓝[≠] x, z∈U from nhdsWithin_le_nhds (h.mem_nhds hx)) (fun z hz => by simp only [G,hz,if_true]))
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=fun z i => F i z)
    (s:=B) (F':=D) (bound:=fun _ : α => C/(r/2)) (ball_mem_nhds x ht)
    (Eventually.mono (h.mem_nhds hx) (fun y hy => (ha y hy).aestronglyMeasurable))
    (ha x hx) hm  hp (integrable_const _) (ae_of_all μ hv)
  exact hh.2.differentiableAt.differentiableWithinAt
end YM.CF.DPress.Analytic

import YM.CF.Vp929.Analysis.Shooting
import Mathlib.Analysis.Calculus.ParametricIntegral
set_option autoImplicit false
noncomputable section
namespace YM.CF.VolumeRate
open Complex Set Filter Metric Topology MeasureTheory
/- adaptation of Mew/Stream, general open set and integral AE -/
theorem integrate_holo {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {μ : Measure α} {F : ℂ → α → E} {U : Set ℂ} {v : α → ℝ} (ho : IsOpen U)
    (h : ∀ᵐ y ∂μ, DifferentiableOn ℂ (fun z=> F z y) U ∧ ∀ z∈ U, ‖F z y‖ ≤ v y)
    (hm : ∀ z∈U,AEStronglyMeasurable (F z) μ) (hv : Integrable v μ) : DifferentiableOn ℂ (fun z=>∫ y, F z y ∂μ) U := by
  classical
  intro x hx; obtain ⟨r,p,hU⟩:= Metric.mem_nhds_iff.mp (ho.mem_nhds hx); let t:=r/3; have ht:0<t:=by unfold t; linarith
  let V:= ball x t
  have hw(z:ℂ)(hz:z∈V): closedBall z t⊆U:= fun y hy=> hU (mem_ball.mpr (lt_of_le_of_lt (dist_triangle y z x) <| by dsimp only [V] at hz; have:= mem_ball.mp hz; have:= mem_closedBall.mp hy; dsimp [t] at *; linarith))
  have hu:V⊆U:= fun z hz=> hw z hz (mem_closedBall_self ht.le)
  let g(y:ℂ)(i:α):=deriv (fun z=>F z i) y
  have hg:AEStronglyMeasurable (g x) μ:=by
    let G(z:ℂ): α→E:= if z∈U then fun i=> (z-x)⁻¹ • (F z i-F x i) else 0
    refine aestronglyMeasurable_of_tendsto_ae (f:=G) (𝓝[≠] x) (fun z=>?_) ?_
    · unfold G; split; next h=>exact ((hm z h).sub (hm x hx)).const_smul _
      exact aestronglyMeasurable_const
    filter_upwards [h] with i hi
    apply Tendsto.congr' _ (hasDerivAt_iff_tendsto_slope.mp ((hi.1 x hx).differentiableAt (ho.mem_nhds hx)).hasDerivAt)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (ho.mem_nhds hx)] with z hz; change _=G _ i; unfold G; rw [if_pos (show z ∈ U from hz)]; rfl
  have hp : ∀ᵐ y ∂μ, ∀ z∈V, ‖g z y‖ ≤ v y/t := by
    filter_upwards [h] with y hy; intro z hz; unfold g; rw [← Complex.cderiv_eq_deriv ho hy.1 ht (hw z hz)]; exact Complex.norm_cderiv_le ht fun w p=>hy.2 w (hw z hz (sphere_subset_closedBall p))
  have he:= hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds x ht) (Eventually.mono (ho.mem_nhds hx) (fun i e=>hm _ e)) (hv.mono' (hm _ hx) (h.mono fun y hy=>hy.2 x hx)) hg hp (hv.div_const _)
    (h.mono fun i hi y hy=> ((hi.1 y (hu hy)).differentiableAt (ho.mem_nhds (hu hy))).hasDerivAt)
  exact he.2.differentiableAt.differentiableWithinAt
end YM.CF.VolumeRate

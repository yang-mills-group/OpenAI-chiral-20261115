import YM.SU5.Reconstruction.Anvil.Roots
import Mathlib.Analysis.Complex.MeanValue
import YM.CF.BProof.Floral.Hol
import Mathlib.Analysis.Calculus.ParametricIntegral
/-! # Press moment Arc center. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Anvil
open Function Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology InnerProductSpace NNReal ENNReal BigOperators Classical
local notation "𝒲"=> Real.circleAverage
local notation "ℭ"=> circleMap 0 1
local notation "π"=> Real.pi
lemma average_of (f:ℂ→ℂ) (p:DifferentiableOn ℂ f Well)(v:ContinuousOn f Pane): 𝒲 f 0 1=f 0:= by
 apply DiffContOnCl.circleAverage; rw [abs_one]; exact ⟨p, (closure_ball (0:ℂ) one_ne_zero) |>.symm ▸ v⟩ -- syntax
lemma average_cost (f:ℂ→ℂ) {Q:ℝ} (p:∀ z∈ Rim, ‖f z‖ ≤ Q) : ‖𝒲 f 0 1‖ ≤ Q:= by
 rw [Real.circleAverage,norm_smul,Real.norm_eq_abs, abs_of_pos (by positivity)];
 exact (mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_of_norm_le_const (fun x _=> p (ℭ x) (circleMap_mem_sphere (0:ℂ) zero_le_one _))) (show 0 ≤ ((2*π)⁻¹:ℝ) from by positivity)).trans_eq (by rw [sub_zero, abs_of_pos Real.two_pi_pos]; field_simp)
section
variable {D:Set ℂ} (P: ℂ→ℂ→ℂ) (Q:ℝ)
-- P takes TIME shift first. Circle arguments don't see parameter changes.
abbrev averages (z:ℂ):= 𝒲 (P z) 0 1
variable (u:IsOpen D) (v :∀ z∈ Rim,DifferentiableOn ℂ (fun x=>P x z) D) (c:∀ x∈ D,ContinuousOn (P x) Rim) (e:∀ x∈ D,∀ z∈ Rim,‖P x z‖ ≤ Q)
local notation "F" x:max => (fun y:ℝ=> P (x:ℂ) (ℭ y))
local notation "G" t:max i:max=> deriv (fun x:ℂ=> P x (ℭ i)) t
include c u v
lemma derivative_contour (x:ℂ)(p:x∈D) : Measurable (fun y=> deriv (fun z:ℂ=>P z (ℭ y)) x):= by
 let l:=𝓝[≠] (0:ℂ); let f (z:ℂ)(y:ℝ):= z⁻¹*(P (x+z) (ℭ y) - P x (ℭ y))
 have ht (i:ℝ): Tendsto (fun t=> f t i) l (𝓝 (G x i)):= ((v _ (circleMap_mem_sphere _ zero_le_one i)).differentiableAt (u.mem_nhds p)).hasDerivAt.tendsto_slope_zero
 have hc(q:ℂ)(w:q∈D): Continuous (F q):=(c q w|>.comp_continuous (continuous_circleMap ..) (circleMap_mem_sphere 0 zero_le_one)) -- tune
 let F' (z:ℂ):= if x+z∈D then f z else fun _=> (0:ℂ); refine measurable_of_tendsto_metrizable' l (f:=F') (fun z =>?_) ((tendsto_pi_nhds.mpr ht).congr' ?_)
 · unfold F'; split_ifs with h; exact (continuous_const.mul ((hc _ h).sub (hc _ p))).measurable; exact measurable_const
 have b: ∀ᶠ i in 𝓝 (0:ℂ),x+i∈D:= by
    have h := (tendsto_const_nhds (x:=x) (f:=𝓝 (0:ℂ))|>.add (tendsto_id (x:=𝓝 (0:ℂ)))) -- tune
    exact h.eventually (u.mem_nhds (by simpa using p))
 exact (b.filter_mono nhdsWithin_le_nhds).mono fun i t=> Eq.symm (if_pos t)
local notation "ℳ"=> volume.restrict (Ioc (0:ℝ) (2*π))
include e
lemma averages_rented : AnalyticOnNhd ℂ (averages P) D:= by
 have A(i:ℝ): ℭ i∈ Rim:= circleMap_mem_sphere (0:ℂ) zero_le_one _; have E(q:ℂ)(e1:q∈D):Continuous (F q):= (c q e1).comp_continuous (continuous_circleMap ..) A
 refine DifferentiableOn.analyticOnNhd ?_ u; intro t h; have K(t): averages P t=( ((2*π)⁻¹:ℝ):ℂ) * ∫ x:ℝ,P t (ℭ x) ∂ℳ := by rw [averages,Real.circleAverage, intervalIntegral.integral_of_le Real.two_pi_pos.le,Complex.real_smul]
 rw [funext K]; apply DifferentiableAt.differentiableWithinAt; apply DifferentiableAt.const_mul
 obtain ⟨r,rp,z⟩ := nhds_basis_closedBall.mem_iff.mp (u.mem_nhds h); let k:=r/2; have kp:= half_pos rp; have kb(i:ℂ)(w:i ∈ ball t k): closedBall i k⊆ D:= by intro y p; apply z; rw [mem_closedBall] at *; have v:= mem_ball.mp w; unfold k at *; linarith [dist_triangle y i t]
 have Dp(i:ℝ)(x:ℂ)(p:x∈ball t k): ‖G x i‖≤ Q/k:= CF.Floral.c_deriv (v (ℭ i) (A i)) kp (kb _ p) (fun _ w=> e _ w _ (A i))
 exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le («F»:= fun z i=>P z (ℭ i)) (F':=fun z i=>G z i) (μ:=ℳ) (bound:=fun _=>Q/k) (ball_mem_nhds t kp)
   ((show ∀ᶠ i in 𝓝 t,i∈D from u.mem_nhds h).mono fun q w=> (E _ w).aestronglyMeasurable)
   (ContinuousOn.integrableOn_Icc ((E t h).continuousOn)|>.mono_set Ioc_subset_Icc_self) ((derivative_contour P u v c t h).aestronglyMeasurable)
   (ae_of_all _ Dp) (by apply integrable_const) (ae_of_all _ fun y s w=> ((v _ (A y)).differentiableAt (u.mem_nhds (kb _ w (mem_closedBall_self kp.le)))).hasDerivAt)).2.differentiableAt
end
end YM.Anvil

import YM.Paley.Line
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ParametricIntegral
/-! # For the complex aperture. Control under the smoothing integral. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConePrice.Storm
open Complex Filter Set Metric MeasureTheory
open scoped Topology NNReal Real

lemma deriv_bound {f:ℂ→ℂ}{r C:ℝ}{x:ℂ}(p:0<r)(v:DifferentiableOn ℂ f (closedBall x r))
    (t:∀ z∈closedBall x r,‖f z‖≤C): ‖deriv f x‖≤ C/r:= by
 apply norm_deriv_le_of_forall_mem_sphere_norm_le p ⟨v.mono ball_subset_closedBall,v.continuousOn.mono closure_ball_subset_closedBall⟩
 intro z h; exact t _ (sphere_subset_closedBall h)

lemma averaging_hol {X:Type*}[MeasurableSpace X]{μ:Measure X}(F:ℂ→X→ℂ) {W:Set ℂ}{x:ℂ}
    {m:X→ℝ} (w:IsOpen W)(p:x∈W)(v:Integrable m μ)(e:∀ y∈W,AEStronglyMeasurable (F y) μ)
    (u:∀ z∈W, ∀ i,‖F z i‖≤ m i)(j:∀ i,DifferentiableOn ℂ (fun x=>F x i) W):
    DifferentiableAt ℂ (fun z=> ∫ t, F z t ∂μ) x := by
 obtain ⟨r,R,h⟩:= Metric.mem_nhds_iff.mp (w.mem_nhds p)
 let D(y:ℂ)(i:X):= deriv (fun z=> F z i) y
 have hd (i:X)(z)(pz:z∈W) : HasDerivAt (fun z=> F z i) (D z i) z:= ((j i).differentiableAt (w.mem_nhds pz)).hasDerivAt
 have hor:0<r/2:=half_pos R
 let S:=ball x (r/2)
 have encl:S ⊆ W:= Set.Subset.trans (ball_subset_ball (by linarith:r/2≤r)) h -- fix
 have hp(y:ℂ)(u:y∈S): closedBall y (r/2) ⊆ W:= by
   intro z hz; apply h; apply mem_ball.mpr
   linarith [mem_closedBall.mp hz, mem_ball.mp (show y∈ball x (r/2) from u),dist_triangle z y x]
 let B(i:X):= m i/r*2
 obtain ⟨a,k⟩:= Filter.exists_seq_tendsto (𝓝[≠] x)
 obtain ⟨n,hn⟩:= eventually_atTop.mp (k.eventually (mem_nhdsWithin_of_mem_nhds (w.mem_nhds p)))
 have H: AEStronglyMeasurable (D x) μ:=by
    let f(l:ℕ)(i:X):= slope (fun z=> F z i) x (a (l+n)); apply aestronglyMeasurable_of_tendsto_ae (f:=f) atTop
    · intro l; change AEStronglyMeasurable (fun i=> (a (l+n)-x)⁻¹ • (F (a (l+n)) i-F x i)) μ
      exact ((e _ (hn (l+n) (by omega))).sub (e x p)).const_smul (a (l+n)-x)⁻¹
    filter_upwards with i
    exact (hd i x p).tendsto_slope.comp (k.comp (Filter.tendsto_add_atTop_nat _))
 refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=S) (F:=F) (F':=D) (bound:=B) (ball_mem_nhds x hor)
    ( (show ∀ᶠ i in 𝓝 x,i∈W from w.mem_nhds p).mono fun z p=> e z p ) (v.mono' (e x p) (ae_of_all _ (u x p))) H
    (ae_of_all μ (fun i z t=> (deriv_bound hor ((j i).mono (hp z t)) (fun y q=>u y (hp z t q) i)).trans_eq (by unfold B; ring))) ?_ (ae_of_all μ (fun i y Y=> hd i y (encl Y)))).2.differentiableAt
 exact (v.div_const _).mul_const _
end YM.ConePrice.Storm

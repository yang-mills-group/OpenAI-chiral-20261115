import GaugeFieldConstruction.BeatificQc
/-!
# First slot derivative on ignorance kernel. Conf tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom.Salam
open Function Filter Set TopologicalSpace YM Analysis MeasureTheory Points Bulb Payroll Metric
open scoped Topology BigOperators ContDiff Classical
variable {n : ℕ}
def WindQc (v:Points n)(K:Points n→ℂ)(p:Test n)(t:ℝ):ℂ:= ∫ x:Points n,p x*K (x+t • v)
lemma windBackQc (v:Points n)(K:Points n→ℂ)(p:Test n)(t:ℝ): WindQc v K p t= ∫ x:Points n,p (x-t • v)*K x:=by
 rw [← integral_add_right_eq_self (fun x:Points n=>p (x-t • v)*K x) (t • v)]; simp only [add_sub_cancel_right,WindQc] -- tune
lemma CostTiltQc (v:Points n)(p:Test n)(K:Points n→ℂ)(c:PlaqueQc K): HasDerivAt (WindQc v K p) (-(tilt v p).applyTo K) 0:=by
 let F:ℝ→Points n→ℂ:= fun t x=> p (x-t • v)*K x; let w:=tilt v p
 let H:ℝ→Points n→ℂ:= fun t x=> -(w (x-t • v)*K x)
 have h₀(t:ℝ)(x:Points n):HasDerivAt (fun t=> F t x) (H t x) t:=by
    have he:HasDerivAt (fun t:ℝ=>x - t • v) (-v) t:= (((hasDerivAt_id' t).smul_const v).const_sub x).congr_deriv (by simp)
    have hp:HasDerivAt (fun t=>F t x) _ t:= ((p.contDiff.differentiable (by simp) (x-t • v)).hasFDerivAt.comp_hasDerivAt _ he).mul_const (K x)
    refine hp.congr_deriv ?_; unfold H w; rw[tilt_pays, map_neg,neg_mul]; rfl
 let T:= tsupport p
 have ht:IsCompact T:=p.hasCompactSupport
 have h:∀ᶠ t in 𝓝 (0:ℝ),∀ x∈T,x+t • v∈conf n:=by
    refine ht.eventually_forall_of_forall_eventually (fun x h=>?_); have p': Continuous (fun u:ℝ×Points n=>u.2+u.1 • v):=continuous_snd.add (continuous_fst.smul continuous_const)
    exact p'.continuousAt.tendsto.eventually ((conf_open _).mem_nhds (by simpa using (show x∈conf _ from p.tsupport_subset h)))
 obtain ⟨r,pR,Q⟩:= Metric.mem_nhds_iff.mp h
 let U:= closedBall (0:ℝ) (r/2); have htU:IsCompact U:= isCompact_closedBall ..
 let G:= fun t:ℝ×Points n=> t.2+t.1 • v; let E:=G '' (U×ˢ T); have he:IsCompact E:=(htU.prod ht).image (continuous_snd.add (continuous_fst.smul continuous_const))
 obtain ⟨V,u,e⟩:=c.tiled E he (image_subset_iff.mpr fun ⟨t,x⟩ k=> Q (closedBall_subset_ball (half_lt_self pR) k.1) x k.2)
 obtain ⟨B,b⟩:=w.hasCompactSupport.exists_bound_of_continuous w.continuous
 let f(x:Points n):ℝ:= E.indicator (fun _=>B*V) x
 have H':Integrable (F 0):=by simpa [F] using BondCostQc p K c
 have φ(t:ℝ):Continuous (fun x:Points n=> x-t • v):= continuous_id.sub continuous_const
 have Hw:Measurable (H 0):=((w.continuous.measurable.comp (φ _).measurable).mul c.bright).neg
 have hm t:Measurable (F t):=(p.continuous.measurable.comp (φ _).measurable).mul c.bright
 have hi:= hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=U) (closedBall_mem_nhds _ (half_pos pR)) (F:=F) (Eventually.of_forall fun t=>(hm t).aestronglyMeasurable) H' Hw.aestronglyMeasurable (show ∀ᵐ x:Points n,∀ t∈U, ‖H t x‖ ≤ f x from ?_) ((integrable_indicator_iff he.measurableSet).mpr (integrableOn_const he.measure_lt_top.ne)) (Eventually.of_forall fun x t _=> h₀ t x)
 · rw [show WindQc v K p=(fun t=>∫ x,F t x) from funext fun t=>windBackQc ..]; refine hi.2.congr_deriv ?_; simp [H,w,Test.applyTo]; exact integral_neg _
 apply Eventually.of_forall; intro x t y
 by_cases p:x∈ E
 · rw[show f x=B*V from indicator_of_mem p _]; unfold H; rw [norm_neg,norm_mul]; exact mul_le_mul (b (x-t • v)) (e x p) (norm_nonneg _) ((norm_nonneg _).trans (b (x-t • v))) -- tune
 have he:x-t • v∉tsupport w:= fun h=> p ⟨(t,x-t • v), ⟨y,dband _ _ h⟩,sub_add_cancel _ _⟩
 unfold H f; rw [image_eq_zero_of_notMem_tsupport he, indicator_of_notMem p]; simp
#check hasDerivAt_integral_of_dominated_loc_of_deriv_le
#print axioms CostTiltQc
end YM.GaugeFieldConstruction.Fathom.Salam

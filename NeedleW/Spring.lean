import NeedleW.Typhon
import Mathlib.Probability.Moments.MGFAnalytic
set_option autoImplicit false
noncomputable section
namespace NeedleW
open MeasureTheory ENNReal NNReal Set Filter ProbabilityTheory
open scoped MeasureTheory ENNReal Topology
abbrev mag(v:ℝ≥0)(t:ℝ):= Real.exp (t * -(v:ℝ))
abbrev lap (μ: Measure ℝ≥0) (t:ℝ):ℝ:=∫ v:ℝ≥0,mag v t ∂μ
lemma opex (v:ℝ≥0)(t:ℝ)(u:0≤t): |mag v t| ≤1:=by rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos u (neg_nonpos.mpr (NNReal.coe_nonneg v)))
variable (μ:Measure ℝ≥0)[IsFiniteMeasure μ]
lemma lap_q{t:ℝ}(u:0≤t): Integrable (fun v:ℝ≥0=> mag v t) μ:= by
 refine (integrable_const (μ:=μ) (1:ℝ)).mono' ?_ (Eventually.of_forall fun v=> by rw [Real.norm_eq_abs]; exact opex _ _ u)
 exact (Real.continuous_exp.comp (continuous_const.mul (NNReal.continuous_coe.neg))).aestronglyMeasurable
lemma summer: AnalyticOnNhd ℝ (lap μ) (Ioi 0):=by
 let X(v:ℝ≥0):=-(v:ℝ)
 change AnalyticOnNhd ℝ (mgf X μ) (Ioi 0)
 exact fun t v=> analyticAt_mgf (interior_maximal (show Ioi (0:ℝ) ⊆ integrableExpSet X μ from fun s p=> (lap_q μ (mem_Ioi.mp p).le)) isOpen_Ioi v)
lemma lap_cost(t:ℝ)(p:0<t):‖lap μ t‖ ≤ μ.real univ:=by
 apply (norm_integral_le_integral_norm _).trans
 have he:= integral_mono (lap_q μ p.le).norm (integrable_const (μ:=μ) (1:ℝ)) (show ∀v:ℝ≥0,‖mag v t‖ ≤ (1:ℝ) from fun v=>by rw [Real.norm_eq_abs]; exact opex v t p.le)
 simpa using he
-- abstract no identity with laplace
lemma health_fin {K:ℝ→ℝ} (h:AnalyticOnNhd ℝ K (Ioi 0))(u:Tendsto K (𝓝[>] 0) atTop):¬ ∀ᶠ t:ℝ in atTop,K t=lap μ t:=by
 rw [eventually_atTop]; rintro ⟨a,g⟩
 let t:=max a 0 +1
 have ht:max a 0<t:=lt_add_one _
 have H0:0<t:=(le_max_right ..).trans_lt ht
 have Hp:K =ᶠ[𝓝 t] lap μ:= (lt_mem_nhds ht).mono fun x e=>g x ((le_max_left ..).trans e.le)
 have hx:= h.eqOn_of_preconnected_of_eventuallyEq (summer μ) isPreconnected_Ioi H0 Hp
 obtain ⟨s,hb,hc⟩:= ((show ∀ᶠ i:ℝ in 𝓝[>] (0:ℝ),0 < i from self_mem_nhdsWithin).and (u.eventually (eventually_gt_atTop (μ.real univ)))).exists
 rw [hx hb] at hc
 exact not_le.mpr hc ((le_abs_self (lap μ s)).trans (lap_cost μ s hb))
#check interior_maximal
#print axioms health_fin
end NeedleW

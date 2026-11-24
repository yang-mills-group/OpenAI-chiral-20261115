import YM.SU5.Reconstruction.Crease.Bravo
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Opera
open Function Set Filter MeasureTheory Complex ProbabilityTheory
open scoped BigOperators Topology InnerProductSpace ComplexOrder NNReal ENNReal Complex Real
noncomputable def spire (t x:ℝ):ℝ:=fizz x* Real.exp (t*x)
lemma spiret (t x:ℝ): fuel t x=(spire t x:ℂ):= by simp [fuel,spire,ofReal_exp]
lemma spiresUp (t:ℝ)(p:t∈ twilight): Integrable (spire t):= by
    have he(x): |spire t x|=spire t x:= abs_of_pos (mul_pos (fizz_pos x) (Real.exp_pos _))
    have h:= (tour (t:ℂ) p).norm; simpa only [spiret,norm_real,Real.norm_eq_abs,he] using h -- tune
section consume
variable (f g:ℝ→ℝ)
-- general nonnegative
noncomputable def cage (t :ℝ):ℝ≥0:= (fizz t*f t).toNNReal
def store := volume.withDensity fun t=>(cage f t:ℝ≥0∞)
structure Oat :Prop where
 b:Continuous f
 nonneg:∀ x,0≤ f x
 afford: ∀ t∈ twilight, Integrable (fun x=> spire t x * f x)
namespace Oat
variable {f g}
variable (p:Oat f)
include p
lemma caged(t:ℝ):(cage f t:ℝ)=fizz t*f t:= Real.coe_toNNReal _ (mul_nonneg (fizz_pos t).le (p.nonneg t))
@[fun_prop] lemma hears : Continuous (cage f) := by unfold cage; have hv:=p.b; fun_prop
lemma paysQuote (t:ℝ)(h:t∈ twilight): t∈ integrableExpSet id (store f):= by
   change Integrable (fun x:ℝ=>Real.exp (t*x)) (volume.withDensity (fun t=>(cage f t:ℝ≥0∞)))
   rw [integrable_withDensity_iff_integrable_coe_smul p.hears.measurable]; simpa only [spire, p.caged,smul_eq_mul,mul_right_comm (fizz _)] using p.afford t h -- mul order tuning
lemma reports(t:ℝ): mgf id (store f) t=∫ x:ℝ, spire t x*f x:=by
 unfold mgf store; rw [integral_withDensity_eq_integral_smul p.hears.measurable]; apply integral_congr_ae; apply Eventually.of_forall; intro x; change (cage f x:ℝ)*_=_; rw [p.caged]; unfold spire; exact mul_right_comm ..
omit p in
private lemma osc : 0∈twilight:= by unfold twilight; simp; positivity -- positivity
lemma skim : IsFiniteMeasure (store f):= by
 apply (integrable_const_iff_isFiniteMeasure (c:=(1:ℝ)) one_ne_zero).mp; let h:=p.paysQuote 0 osc; change Integrable _ _ at h; simpa using h
lemma compares (q:Oat g)(h:∀ θ∈ twilight,(∫ x:ℝ,spire θ x*f x)=∫ x:ℝ,spire θ x*g x): f=g:=by
 let y:=store f; let z:=store g
 letI:IsFiniteMeasure y:=p.skim; letI:IsFiniteMeasure z:=q.skim
 have eq:y=z:=by
    let A:={x:ℂ| x.re∈twilight}
    apply Measure.ext_of_charFun; funext t; rw [← complexMGF_id_mul_I,←complexMGF_id_mul_I];
    have he (M:ℝ→ℝ)(q:Oat M):AnalyticOnNhd ℂ (complexMGF id (store M)) A:= by
       letI:=q.skim; intro x hx; apply analyticAt_complexMGF; exact (interior_maximal (fun v e=> q.paysQuote v e) isOpen_Ioo) hx
    refine (he f p).eqOn_of_preconnected_of_frequently_eq (he g q) ((convex_Ioo _ _).linear_preimage Complex.reCLM.toLinearMap).isPreconnected (z₀:=0) (show (0:ℂ)∈A from osc) ?_ (show (↑t * I:ℂ)∈A from ?_) -- tune
    · intro w; have ht:Tendsto ofReal (𝓝[>] (0:ℝ)) (𝓝[≠] (0:ℂ)):= by
          apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
          · simpa using (continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
          exact (show ∀ᶠ x in 𝓝[>] (0:ℝ),x∈Ioi (0:ℝ) from self_mem_nhdsWithin).mono fun x hx=> ofReal_ne_zero.mpr (mem_Ioi.mp hx).ne'
      obtain ⟨x,k,v⟩:= ((ht.eventually w).and (mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds osc))).exists
      apply k; rw [complexMGF_ofReal,complexMGF_ofReal,p.reports,q.reports,h x v]
    change (↑t*I:ℂ).re∈ twilight; simpa [mul_re] using osc
 have ht: AEMeasurable (fun t:ℝ=>(cage f t: ℝ≥0∞)) volume:= by have e:=p.hears; fun_prop
 have hh: AEMeasurable (fun t:ℝ=>(cage g t:ℝ≥0∞)) volume:= by have e:=q.hears; fun_prop
 refine MeasureTheory.Measure.eq_of_ae_eq (μ:=volume) ?_ p.b q.b
 have hv := (withDensity_eq_iff_of_sigmaFinite ht hh).1 eq; filter_upwards [hv] with x hx; apply mul_left_cancel₀ (fizz_pos x).ne'; rw [← p.caged, ← q.caged, ENNReal.coe_injective hx]
end Oat
end consume
@[fun_prop] lemma spire_cont (θ): Continuous (spire θ):= by unfold spire; fun_prop
lemma fiat (θ t:ℝ):0< spire θ t:=mul_pos (fizz_pos _) (Real.exp_pos _)
lemma stick (θ:ℝ)(e:θ∈ twilight)(f:ℝ→ℝ)(p:Continuous f)(M:ℝ)(m:∀ x, ‖f x‖ ≤ M): Integrable (fun x=> spire θ x*f x):= by
 apply ((spiresUp θ e).norm.mul_const M).mono' ?_ ?_ -- tune
 · exact (show Continuous (fun x=> spire θ x*f x) by fun_prop).aestronglyMeasurable
 exact Eventually.of_forall (fun x=> by change ‖_ * _‖ ≤ _; rw [norm_mul]; gcongr; exact m x)
lemma informs {f:ℝ→ℝ}(p:Continuous f){M:ℝ}(m:∀ x,‖f x‖≤ M)(e:∀ θ∈ twilight, (∫ x,spire θ x*f x)=0)(t:ℝ): f t=0:= by
 let g(x:ℝ):= M+f x; have ht(x:ℝ): g x≥0:= by have a := (abs_le.mp (show |f x| ≤ M from m x)).1; unfold g; linarith
 let F(x:ℝ):=M; have hu:Oat F:=⟨continuous_const,fun _ => le_trans (norm_nonneg _) (m 0),fun θ h=>(spiresUp θ h).mul_const M⟩
 have he:Oat g:=by refine ⟨continuous_const.add p,ht,fun θ h=>?_⟩; simp_rw [g,mul_add]; exact (hu.afford θ h).add (stick θ h f p M m)
 have hz:g t= M:= congrFun (he.compares hu fun θ h=> by unfold g F; simp only [mul_add]; rw [integral_add ((spiresUp θ h).mul_const M) (stick θ h f p M m), e θ h,add_zero]) t
 unfold g at hz; linarith
lemma cup_prices (θ:ℝ)(e:θ∈ twilight)(f:ℝ→ℂ)(p:Continuous f)(M:ℝ)(m:∀ x, ‖f x‖≤ M): Integrable (fun x=>cup θ x*f x):=by
 apply ((redeem θ e).norm.mul_const M).mono' (show AEStronglyMeasurable _ _ from (by fun_prop))
 exact Eventually.of_forall (fun x=> by change ‖_ * _‖ ≤ _; rw [norm_mul]; gcongr; exact m x)
lemma consumes {f:ℝ→ℂ}(p:Continuous f){M:ℝ}(m:∀ x,‖f x‖≤ M)(h:∀ θ∈ twilight,(∫ x,cup θ x*f x)=0)(x:ℝ):f x=0:=by
 have ht(s:ℂ →L[ℝ] ℝ):s (f x)=0:=by
   apply informs (f:=s ∘ f) (s.continuous.comp p) (M:=‖s‖*M) (fun y => (s.le_opNorm (f y)).trans (mul_le_mul_of_nonneg_left (m y) (norm_nonneg _)))
   intro θ g; have he(t:ℝ): cup θ t*f t= tune (-θ)/2 * (spire θ t • f t):=by rw [cup,spiret,Complex.real_smul]; ring
   have hv:= h θ g; simp_rw [he] at hv; rw [integral_const_mul, mul_eq_zero, or_iff_right (show tune (-θ)/2 ≠0 from div_ne_zero (tune_not _) (by norm_num))] at hv
   have hm:= cup_prices θ g f p M m; simp_rw [he] at hm; rw [integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (div_ne_zero (tune_not _) (by norm_num)))] at hm
   have hu:= s.integral_comp_comm hm; simpa only [hv,map_zero,map_smul,smul_eq_mul, Function.comp_apply] using hu -- tune
 apply Complex.ext; exact ht Complex.reCLM; exact ht Complex.imCLM
end YM.Opera

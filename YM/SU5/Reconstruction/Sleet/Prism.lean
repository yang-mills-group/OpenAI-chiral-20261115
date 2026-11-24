import YM.SU5.Reconstruction.Sleet.Beryl
/-! # Execution of Wick curve continuation on simultaneous slot queries. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConePrice.Storm
open Set Filter MeasureTheory Complex Sail Metric
open scoped Topology NNReal Real Classical
variable {F:ℝ→ℂ→ℂ}{G:ℂ→ℝ→ℂ}{d C:ℝ}(κ:Gust d C F G)
def ice (n:ℕ):ℝ:=n+1
lemma heatk (n:ℕ):0 < ice n:=by unfold ice; positivity
def leadStream: Filter ℕ:= (Ultrafilter.of (atTop:Filter ℕ))
def hatch(F:ℝ→ℂ→ℂ)(z v:ℂ):ℂ:= lim (leadStream.map (fun k=> crystal F (ice k) z v))
local instance: leadStream.NeBot:= by unfold leadStream; infer_instance
include κ
lemma tend_lead(z v:ℂ)(p:chamber d z v): Tendsto (fun k=>crystal F (ice k) z v) leadStream (𝓝 (hatch F z v)):= by
 let a:= (Ultrafilter.of (atTop:Filter ℕ)).map fun k=>crystal F (ice k) z v
 obtain ⟨x,b,h⟩:= (isCompact_closedBall (0:ℂ) C).ultrafilter_le_nhds a (by
   apply le_principal_iff.mpr; change ∀ᶠ i in leadStream,crystal F (ice i) z v∈closedBall 0 C; apply Eventually.of_forall; intro i; rw [Metric.mem_closedBall,dist_zero_right]; exact middle_power κ (ice i) (heatk i).ne' z v p)
 change (a:Filter ℂ)≤ 𝓝 (lim (a:Filter ℂ)); rw [lim_eq h]; exact h
lemma hatch_power(z v:ℂ)(p:chamber d z v): ‖hatch F z v‖≤ C:= le_of_tendsto (tend_lead κ z v p).norm (Eventually.of_forall (fun i=>middle_power κ (ice i) (heatk i).ne' z v p))
lemma hatch_curve{W:Set ℂ}{f g:ℂ→ℂ}(h:IsOpen W)(p:∀ z∈W,chamber d (f z) (g z))(e:AnalyticOnNhd ℂ f W)(k:AnalyticOnNhd ℂ g W): AnalyticOnNhd ℂ (fun z=> hatch F (f z) (g z)) W:= by
 open CF.Floral in
 exact (chalk h (l:=leadStream) (F:=fun n z=>crystal F (ice n) (f z) (g z)) (Eventually.of_forall fun n=>(crystal_turn κ _ h (fun z Z=> (p z Z).north) e k).differentiableOn) (Eventually.of_forall fun n z Z=>middle_power κ (ice n) (heatk n).ne' (f z) (g z) (p z Z)) (fun z Z=> tend_lead κ _ _ (p z Z))).analyticOnNhd h -- signature

lemma real_tides(x v:ℝ): Tendsto (fun n=> crystal F (ice n) x v) atTop (𝓝 (F x v)):=by
 let J:=fun (n:ℕ) (t:ℝ)=> (glimmer t:ℂ)*G ((↑(t/(ice n)):ℂ)+x) v; let K(t:ℝ):= (glimmer t:ℂ)*G (x:ℂ) v
 let W(t:ℝ):= glimmer t*C
 have h(n t): (↑(t/ice n):ℂ)+(x:ℂ)∈ slit d:=by rw [←Complex.ofReal_add]; exact slit_ground d κ.pos _
 have j: Tendsto (fun n=> ∫ t:ℝ,J n t) atTop (𝓝 (∫ t:ℝ,K t)):=by
    apply tendsto_integral_of_dominated_convergence W _ (glimmer_ok.mul_const C) _ _
    · intro n; refine (Continuous.mul ?_ ((κ.guides v).continuousOn.comp_continuous (f:=fun t:ℝ=> (↑(t/ice n):ℂ)+(x:ℂ)) ?_ (h n))).aestronglyMeasurable
      · unfold glimmer;fun_prop
      fun_prop
    · intro n; apply ae_of_all; intro t; unfold J W; rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (glimmer_pos _)]; exact mul_le_mul_of_nonneg_left (κ.charge v _ (h n _)) (glimmer_pos _)
    apply ae_of_all; intro t; apply tendsto_const_nhds.mul (((κ.guides v x (slit_ground d κ.pos x)).continuousAt).tendsto.comp _)
    suffices hx:Tendsto (fun n=> (↑(t/ice n):ℂ)) atTop (𝓝 0) by simpa only [zero_add] using hx.add_const (x:ℂ)
    have ht:Tendsto ice atTop atTop:= tendsto_atTop_add_const_right atTop _ tendsto_natCast_atTop_atTop -- tune
    have hu:Tendsto (fun n=> t/ice n) atTop (𝓝 0):= by simp_rw [div_eq_mul_inv]; simpa using (tendsto_inv_atTop_zero.comp ht).const_mul t
    simpa only [Function.comp_def, ofReal_zero] using (Complex.continuous_ofReal.tendsto 0).comp hu
 rw [show (fun n=>crystal F (ice n) x v)=(fun n=>ported G (ice n) x v) from funext fun n=> ported_real κ _ (heatk n).ne' x v,κ.meets]; unfold K at j; rw [integral_mul_const,integral_complex_ofReal,glimmer_full,ofReal_one,one_mul] at j; exact j
lemma hatch_real(x v:ℝ): hatch F x v = F x v := tendsto_nhds_unique (tend_lead κ _ _ (by simp [chamber,κ.pos])) ((real_tides κ x v).mono_left (Ultrafilter.of_le atTop))
-- actually continue both original prices
lemma hatch_lateral(v:ℝ): EqOn (fun z=> hatch F z v) (fun z=> G z v) (slit d):= pioneer (slit_connected d) (slit_ground d κ.pos 0) (-1) 1 (by norm_num)
   (hatch_curve κ (slit_open d) (fun z Z=> (by change |z.im|+|(v:ℂ).im|<d; simpa using (show |z.im|<d from Z))) (fun z _=>analyticAt_id) analyticOnNhd_const) (κ.guides v) (fun x _=> (hatch_real κ x v).trans (κ.meets x v)) -- tune
lemma hatch_top(x:ℝ): EqOn (fun z=> hatch F x z) (F x) (slit d):= pioneer (slit_connected d) (slit_ground d κ.pos 0) (-1) 1 (by norm_num)
   (hatch_curve κ (slit_open d) (fun z Z=> (by change |(x:ℂ).im|+|z.im|<d; simpa using (show |z.im|<d from Z))) analyticOnNhd_const (fun z _=>analyticAt_id)) (κ.usable x) (fun v _=> hatch_real κ x v)
end YM.ConePrice.Storm

import YM.SU5.Cheer.Heart
/-! # Full timelike reach in sector & boundary readings. -/
set_option autoImplicit false
set_option maxHeartbeats 240000
noncomputable section
namespace YM.Cheer
open Function Metric Set Filter Complex GaussianFourier MeasureTheory Measure Mink
open scoped Real Topology NNReal ENNReal InnerProductSpace BigOperators
abbrev Pasture:= {r:ℝ//0 < r}
local notation "μ"=> (volume : Measure SpinP)
local notation "ν"=> (volume : Measure SpinTrack)
local notation "π'"=> ((Real.pi:ℝ):ℂ)
variable (g:SpinTrack → ℝ≥0∞)(r:Pasture)
local notation "p↑"=> ((r.val:ℝ):ℂ)
def warden (z:SpinTrack):ℝ := π ⁻¹ ^4 * ‖lightK 0 (p↑) z‖
def crest(r:Pasture)(z:SpinTrack):ℝ≥0∞:= ENNReal.ofReal (warden r z)
def footpath(r:Pasture):Measure SpinTrack:= (ν).withDensity (crest r)
-- notation fix
lemma warden_eq (z:SpinTrack) : warden r z = π ⁻¹ ^4* (bill z.1 * Real.exp (- (r.val*time (apex z)))):= by
 unfold warden lightK warmK; rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,abs_of_nonneg (bill_p _)]; simp
lemma open_road(z:SpinTrack)(h:z.1≠0): 0< warden r z:=by rw [warden_eq]; exact mul_pos (by positivity) (mul_pos (bill_vis h) (Real.exp_pos _))
lemma ok_warden(z:SpinTrack): 0 ≤ warden r z:= by unfold warden; positivity
@[fun_prop] lemma warden_cont:Continuous (warden r):= by unfold warden lightK warmK; fun_prop
@[fun_prop] lemma crest_cont:Continuous (crest r):= ENNReal.continuous_ofReal.comp (warden_cont r)
instance ample : IsFiniteMeasure (footpath r):=by refine isFiniteMeasure_withDensity_ofReal ?_; exact ((merit 0 (show 0 < (p↑).re from r.property)).norm.const_mul (π ⁻¹ ^4)).2
abbrev Prom : SpinTrack × SpinTrack → E4:=fun z=> apex z.1+apex z.2
@[fun_prop] lemma prom_cont : Continuous Prom:=by unfold Prom; fun_prop
def moving (r s: Pasture): Measure E4 := ((footpath r).prod (footpath s)).map Prom
instance (s:Pasture) : IsFiniteMeasure (moving r s):=by unfold moving; infer_instance
variable (s:Pasture)
variable (p:Space3)(t:ℂ)
-- complex-time argument. actual UV t. ensure `e^{ -E (T + t)}` damp tb ≥0. note no need integrability for μ.prod factor though holds.
def tendsK (p:Space3)(t:ℂ)(w:E4):ℂ:= Complex.exp ((inner ℝ (spatial w) p:ℂ)*I - t*(time w:ℂ))
@[fun_prop] lemma airy : Continuous (tendsK p t):=by unfold tendsK; fun_prop
def plum (p:Space3)(t:ℂ):ℂ:= cab p t/(π'^2 * wind p t ^ 2)
@[simp] lemma upfront (z:SpinTrack): tendsK p t (apex z)= warmK p t z:=by rw [tendsK,warmK,pierS]
lemma together (u v:E4): tendsK p t (u+v)=tendsK p t u*tendsK p t v:=by
 unfold tendsK; rw [← Complex.exp_add,rest_add,inner_add_left,clock_add]; push_cast; ring_nf
lemma withinK(x:E4)(h:0 ≤ t.re)(u:0 ≤ time x): ‖tendsK p t x‖≤1:=by rw [tendsK,Complex.norm_exp]; simp [mul_nonneg h u]
lemma pony (v:SpinTrack) : (crest r v).toReal • warmK p t v= (π'⁻¹ ^4)* lightK p (t + p↑) v:=by
 rw [crest, ENNReal.toReal_ofReal (ok_warden ..), warden_eq]; simp only [Complex.real_smul]; unfold lightK warmK; push_cast
 generalize (inner ℝ (shoal v) p:ℂ)*I=a; rw [show a-(t+p↑)*(time (apex v):ℂ) = -(r.val:ℂ)*↑(time (apex v))+(a-t*↑(time (apex v))) by ring,Complex.exp_add]; ring_nf -- tune
variable (h: 0 ≤ t.re)
include h
lemma pay : (∫ x, warmK p t x ∂ footpath r)=plum p (t + p↑):=by
 have he:0<(t + p↑).re:= add_pos_of_nonneg_of_pos h r.property
 rw [footpath, integral_withDensity_eq_integral_toReal_smul (crest_cont r |>.measurable) (ae_of_all _ (fun _=> ENNReal.ofReal_lt_top)), plum]
 simp_rw [pony]; rw [integral_const_mul, show ν=(μ).prod μ from rfl, both_buy _ he]; field_simp [wind_ne p _ he,Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
lemma consecrated : (∫ x, tendsK p t x ∂ moving r s)=plum p (t+p↑)*plum p (t+ ↑(s.val)):=by
 rw [moving, integral_map prom_cont.measurable.aemeasurable (airy p t |>.aestronglyMeasurable)]
 unfold Prom; simp_rw [together,upfront]; rw [integral_prod_mul («μ»:=(footpath r)),pay,pay] <;> assumption
end YM.Cheer
#print axioms YM.Cheer.consecrated

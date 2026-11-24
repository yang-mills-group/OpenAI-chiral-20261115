import YM.CF.BPress.Port.Nook
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
/-! iid truncated Gaussian on Pack. finite constants uniform for every y and fixed D. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Port
open Function Filter MeasureTheory LocalH Lattice Wilson RG Precision Grid Cube Bands Pressure Wealth Finset Weave Metric
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ENNReal
open SU Gauge
attribute [local instance] Gauge.frobInner
variable {s:Side}{B:BandWidth}(X:Bands s B)(D:ℕ)(y:ℝ)
def low_v (v:Pack D):= Real.exp (- ‖v‖^2/2)
def truncv := (drift y)^2
def stageW (t:ℝ):= closedBall (0: Pack D) t
def truncate (v:Pack D) := (stageW D (truncv y)).indicator (low_v D) v
def billion (r:ℝ):= ∫ v in stageW D r, low_v D v
abbrev N_v:= billion D (truncv y)
def vcost (v:Pack D) := (N_v D y)⁻¹* truncate D y v
def volts := volume.withDensity (ENNReal.ofReal ∘ vcost D y)
lemma sw_meas (r:ℝ) : MeasurableSet (stageW D r):= isClosed_closedBall.measurableSet
lemma trunc_eq (v:Pack D) : truncate D y v=if ‖v‖≤truncv y then low_v D v else 0:=by simp [truncate,stageW,Set.indicator]
lemma v_cont : Continuous (low_v D):=by unfold low_v; fun_prop
@[fun_prop] lemma truncM : Measurable (truncate D y):= (v_cont D).measurable.indicator (sw_meas ..)
lemma charge_integral (p:ℝ)(e:0<p): Integrable fun x:Pack D=> Real.exp (-p * ‖x‖^2) :=by
 have he:= (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (b:=(p:ℂ)) e 0 (0:Pack D)).norm; simpa [Complex.norm_exp,pow_two,Complex.mul_re] using he
lemma cold_integral : Integrable (low_v D):=by
 have he:=charge_integral D (1/2) (by norm_num); convert! he using 1; ext i; unfold low_v; ring_nf
lemma c_pos (v:Pack D) : 0 < low_v D v:= Real.exp_pos _
lemma trunc_pos (y:ℝ): 1 ≤ truncv y:= one_le_pow₀ (drift_one y)
lemma cage_pos (r:ℝ)(t:0<r): 0 < billion D r:= (integral_pos_iff_support_of_nonneg (fun v=>(c_pos D v).le) (cold_integral D).integrableOn).mpr (by
 rw [show Function.support (low_v D)=Set.univ from Set.eq_univ_of_forall (fun v=>(c_pos D v).ne'),Measure.restrict_apply_univ]; exact lt_of_lt_of_le (isOpen_ball.measure_pos volume ⟨0,mem_ball_self t⟩) (measure_mono ball_subset_closedBall))
def minpay (D:ℕ) := billion D 1
def maxpay (D:ℕ) := ∫ v, low_v D v
lemma pays : N_v D y ∈ Set.Icc (minpay D) (maxpay D):= by
 constructor
 · exact setIntegral_mono_set (cold_integral D).integrableOn (.of_forall fun v=>(c_pos D v).le) (.of_forall fun _ h=> closedBall_subset_closedBall (trunc_pos y) h)
 unfold maxpay; rw [←setIntegral_univ]; exact setIntegral_mono_set (cold_integral D).integrableOn (.of_forall fun v=>(c_pos D v).le) (.of_forall fun i _=>Set.mem_univ i)
lemma v_pos : 0 < N_v D y:= cage_pos D _ (zero_lt_one.trans_le (trunc_pos y))
lemma v_meas : Measurable (vcost D y):= measurable_const.mul (truncM ..)
lemma v_nonneg (x:Pack D):0≤ vcost D y x:= by unfold vcost; rw [trunc_eq]; have h:= v_pos D y; split <;> positivity [c_pos D x]
lemma v_int : Integrable (vcost D y):= Integrable.const_mul ((cold_integral D).indicator (sw_meas ..)) _
lemma v_intE : (∫ v, vcost D y v)=1:=by unfold vcost truncate; rw [integral_const_mul,integral_indicator (sw_meas ..)]; exact inv_mul_cancel₀ (v_pos D y).ne'
instance : IsProbabilityMeasure (volts D y):=⟨by unfold volts; rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]; exact (ofReal_integral_eq_lintegral_ofReal (v_int D y) (.of_forall fun v=> v_nonneg D y v)).symm.trans (by rw [v_intE,ENNReal.ofReal_one])⟩
-- gaussian cap tail
lemma tailw (D:ℕ)(v:ℝ) : MeasurableSet {x:Pack D|v≤‖x‖}:= measurableSet_le measurable_const continuous_norm.measurable
def hBound (D:ℕ) := (minpay D)⁻¹* (∫ v:Pack D, Real.exp (-(1/4)*‖v‖^2))
lemma hbound_pos : 0 < hBound D:= by have he:0<minpay D:= cage_pos _ _ (by norm_num); unfold hBound; exact mul_pos (inv_pos.mpr he) (by exact integral_pos_of_integrable_nonneg_nonzero (x:=0) (by fun_prop) (charge_integral D _ (by norm_num)) (fun i=> (Real.exp_pos _).le) (Real.exp_ne_zero _)) -- tune
lemma vcost_tail (v:ℝ) (p:0≤ v) : volts D y {x:Pack D|v ≤ ‖x‖} ≤ ENNReal.ofReal (hBound D * Real.exp (-(1/4)*v^2)):=by
 unfold volts; rw [withDensity_apply _ (tailw D v)]; let S:={x:Pack D|v ≤ ‖x‖}; let μ:=(volume: Measure (Pack D)).restrict S; change (∫⁻ x, ENNReal.ofReal (vcost D y x) ∂μ) ≤ _; rw [← ofReal_integral_eq_lintegral_ofReal (v_int D y).integrableOn (.of_forall fun x=>v_nonneg D y x)]; apply ENNReal.ofReal_le_ofReal; let Z:= fun v:Pack D=> Real.exp (-(1/4)*‖v‖^2); let A:= Real.exp (-(1/4)*v^2); let K:= (minpay D)⁻¹; have he:0 ≤ K:= (inv_pos.mpr (cage_pos _ _ zero_lt_one)).le; have hv:0 ≤ A:= (Real.exp_pos _).le; have hx:=charge_integral D (1/4) (by norm_num)
 apply le_trans (b:=∫ x in S, K*(A* Z x)) ?_ ?_
 · apply setIntegral_mono_on (v_int D y|>.integrableOn) ((hx.const_mul A).const_mul K|>.integrableOn) (tailw D v); intro i hi; unfold vcost; rw [trunc_eq]; split; next e=>
     apply mul_le_mul (inv_anti₀ (cage_pos _ _ zero_lt_one) (pays D y).1) ?_ (c_pos ..|>.le) he; unfold low_v A; rw [←Real.exp_add]; apply Real.exp_monotone; nlinarith only [pow_le_pow_left₀ p (show v≤‖i‖ from hi) 2]
   next t=> rw [mul_zero]; positivity
 rw [integral_const_mul,integral_const_mul]; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (setIntegral_le_integral hx (.of_forall fun x=> (Real.exp_pos _).le)) hv) he); exact Eq.le (by unfold hBound K A; ring) -- tune order
end YM.CF.BPress.Port

import YM.SU5.Reconstruction.Sleet.Thaw
import YM.SU5.Reconstruction.Sleet.Permafrost
/-! # Quantitative ticket for PVM of one vector -/
set_option autoImplicit false
noncomputable section
namespace YM.ConePrice.Storm
open Set Filter Metric Function MeasureTheory Spectral Analysis
open scoped Topology ComplexOrder NNReal ENNReal InnerProductSpace Real Classical
open Complex CF.Buffered.Afterglow.Tower MeshClock Germ SelectionAnalysis OS Semigroup Picket Boundary Probe Snowball
variable {H:Hilbert} {a:Axis} (S:OS.Semigroup H a)
def spatialP(b:Axis)(p:E4):ℝ:= p b
def heightP(a:Axis)(p:E4):ℝ:= max 0 (p a)
def tundra (j:Axis)(f:H) (r t:ℝ):= metre (S.ℚmeasure.diagonal f) (heightP a) (spatialP j) r t
local notation "P" => S.ℚmeasure
local notation "𝔪" x:max => S.ℚmeasure.diagonal x
variable (j:Axis)
lemma shift_dials (h:j≠a)(f:H)(s:ℝ≥0)(t:ℝ): tundra S j f s t= inner ℂ f (S.U (t • Picket.cross a j h) (S.E s f)):=by
 unfold tundra metre; rw [ConePrice.damped]; refine integral_congr_ae ?_; filter_upwards [Measure.support_mem_ae (μ:=𝔪 f)] with z Z
 change (↑(Real.exp _) :ℂ)* Complex.exp _ = plane z (t • basis j)*Complex.exp _
 unfold heightP spatialP plane; rw [max_eq_right (S.nonneg f Z),real_inner_smul_right, innerB]; push_cast; rw [mul_comm]; congr 2 <;> ring_nf <;> simp
lemma perennity (h:j≠a)(f:H)(s:ℝ≥0): Continuous (tundra S j f s):=by rw [show tundra S j f s=(fun t:ℝ=>_) from funext (shift_dials S j h f s)]; exact continuous_const.inner ((S.continuousU _).comp (by fun_prop))
-- tension bound suff per one axis. use in transferred spacecraft.
lemma retunes (h:j≠a)(f:H)(p:∀ y∈(𝔪 f).support,|y j|≤ y a) (t:ℝ≥0) :
    let T:=t.val • Picket.cross a j h
    ‖S.U T (S.E t f)-S.E t f‖≤‖f-S.E t f‖:=by
 intro T; rw [price]; apply integral_nonpos_of_ae
 filter_upwards [Measure.support_mem_ae (μ:=𝔪 f)] with y Y
 rw [tension_true, ← cone_mean]; change 2*(1-Real.cos (inner ℝ y (t.val • basis j)))*_ - _ ≤0; rw [real_inner_smul_right,Picket.innerB, sub_nonpos]; let b:= (t:ℝ)* y j; let u:= y a * (t:ℝ); have hv:0≤ u:=mul_nonneg (S.nonneg f Y) t.property
 have hz:|b|≤ u:=by unfold u b; rw [abs_mul,show |(t:ℝ)|=(t:ℝ) from abs_of_nonneg t.property,mul_comm (y a)]; exact mul_le_mul_of_nonneg_left (p y Y) t.property
 change 2*(1-Real.cos b)*_≤_
 rw [neg_mul]; change 2*(1- Real.cos b)*Real.exp (-u)^2 ≤(1-Real.exp (-u))^2
 calc
  _ ≤ b^2*Real.exp (-u)^2:=mul_le_mul_of_nonneg_right (by linarith [Real.one_sub_sq_div_two_le_cos (x:=b)]) (sq_nonneg _)
  _ ≤ u^2* Real.exp (-u)^2:=by rw [←sq_abs b]; gcongr
  _ ≤ _:= by rw [←mul_pow]; exact pow_le_pow_left₀ (by positivity) (exp_board hv) _
end YM.ConePrice.Storm

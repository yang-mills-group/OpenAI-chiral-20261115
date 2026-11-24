import YM.SU5.Reconstruction.Cone.Kernels
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
/-!
# Exact criterion
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section

namespace YM.ConePrice
open Function Set Filter MeasureTheory Measure InnerProductSpace Spectral OS Semigroup Real
open scoped BigOperators NNReal ENNReal Topology InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S : OS.Semigroup H a)
local notation "P" => S.ℚmeasure
local notation "𝔪" x:max => S.ℚmeasure.diagonal x
section represents

lemma cone_mean (x : Cross a) (p : E4) : inner ℝ p x.val= inner ℝ (SEP a p) x := by
  change _ = inner ℝ (p-p a • basis a) x.val
  rw [inner_sub_left, real_inner_smul_left, basis_inner, show x.val a=0 from x.property]; ring
local notation "D" p:max t:max => exp (-(p a)*(t:ℝ))
-- notation a in source? lean inserts unbound a; used only under section var
lemma tension_true (x : Cross a) (t : ℝ≥0) (p : E4) : tension x t p =
    2*(1-cos (inner ℝ (SEP a p) x))*(D p t)^2-(1-D p t)^2 := by
  rw [tension,amp_time,amp_time,amplitude,cone_mean,NNReal.coe_add,mul_add,exp_add]; ring
lemma trig_rel (x : Cross a) (t : ℝ≥0) (p : E4) : tension x t p =
    (2 * sin (inner ℝ (SEP a p) x / 2) * (D p t))^2-(1-(D p t))^2 := by
  rw [tension_true]
  conv_lhs => rw [← show 2*(inner ℝ (SEP a p) x/2) = inner ℝ (SEP a p) x from by ring, cos_two_mul_eq_one_sub]
  ring
lemma exp_board {u : ℝ} (_h : 0 ≤ u) : u * exp (-u) ≤ 1-exp (-u) := by
  have hp := mul_le_mul_of_nonneg_right (Real.add_one_le_exp u) (Real.exp_pos (-u)).le
  rw [← Real.exp_add, add_neg_cancel, exp_zero] at hp; linarith
lemma tension_front {x : Cross a} {t : ℝ≥0} (e : ‖x‖≤ (t:ℝ)) (p : E4) (v : p∈front a) : tension x t p ≤ 0 := by
  rw [tension_true, sub_nonpos]; set w := inner ℝ (SEP a p) x
  set u := p a*(t:ℝ) with fu
  have hu : 0≤ p a := (norm_nonneg _).trans v; have hv : 0 ≤ u := by dsimp only [u]; positivity
  have hn : |w| ≤ u := le_trans (abs_real_inner_le_norm (SEP a p) x) (mul_le_mul v e (norm_nonneg _) hu)
  calc
    _ ≤ w^2*(D p t)^2 := mul_le_mul_of_nonneg_right (by linarith [Real.one_sub_sq_div_two_le_cos (x:=w)]) (sq_nonneg _)
    _ ≤ u^2* (D p t)^2 := by rw [← sq_abs w]; gcongr
    _ ≤ (1-(D p t))^2 := by rw [← mul_pow,neg_mul,← fu]; exact pow_le_pow_left₀ (by positivity) (exp_board hv) _
end represents
section weight
lemma price (x : H) (y : Cross a) (t : ℝ≥0) : ‖S.U y (S.E t x)-S.E t x‖≤‖x-S.E t x‖ ↔ ∫ p, tension y t p ∂𝔪 x ≤ 0 := by
  rw [← pressure_amount,sub_nonpos,sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
lemma restrictP {t} (h : MeasurableSet t) (x : H) : (P).diagonal ((P).region t x) = ((P).diagonal x).restrict t := by
  ext s hs
  rw [Measure.restrict_apply hs]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp -- tune
  change ((P).diagonal _).real _=((P).diagonal x).real _
  rw [(P).same hs,(P).same (hs.inter h),← ContinuousLinearMap.comp_apply, (P).joins hs h]
lemma tension_point (y : Cross a) (t : ℝ≥0) (h : ∀ x : H, ‖S.U y (S.E t x)- S.E t x‖ ≤ ‖x-S.E t x‖) :
    ∀ v : H,∀ p ∈ (𝔪 v).support, tension y t p ≤ 0:= by
  intro v p hp
  refine Measure.support_subset_of_isClosed (t:={r : E4 | tension y t r ≤ 0}) (isClosed_le (by fun_prop) continuous_const) ?_ hp
  apply ae_le_of_forall_setIntegral_le (can_enter ..) (integrable_const (0:ℝ)); intro r hr _
  simpa [← restrictP S hr] using (show ∫ q, tension y t q ∂(P).diagonal ((P).region r v) ≤ 0 from (price ..).1 (h ((P).region r v)))
lemma forward_ae (x : H) (v : Forward S) : ∀ᵐ p ∂𝔪 x,p∈front a := by
  apply (ae_iff ..).mpr; change (P).diagonal x (front a)ᶜ=0; exact ((P).null_pair (closed_front a).isOpen_compl.measurableSet x).2 (by rw [v]; rfl)
end weight
section location
/-- Need only tiny stamp bills (price for GRID subset exported after proving continuity of any chart). -/
def Cools (e : ℝ): Prop := ∀ (t : ℝ≥0), 0 < t → (t:ℝ)<e → ∀ (x : Cross a), ‖x‖ ≤ (t:ℝ) →
  ∀ v : H, ‖S.U x (S.E t v)-S.E t v‖ ≤ ‖v-S.E t v‖
lemma tension_bill {y : Cross a} (x : H) {t : ℝ≥0} (e : ‖y‖≤ (t:ℝ)) (h : Forward S) : ‖S.U y (S.E t x)-S.E t x‖ ≤ ‖x-S.E t x‖ := by
  rw [price]; apply integral_nonpos_of_ae; exact (forward_ae S x h).mono (fun r v=>tension_front e r v)
private lemma surf (e : ℝ) (p : E4) (b : 0 < e) (_u : 0 ≤ p a)
    (he : ∀ t : ℝ≥0, 0 < t → (t:ℝ)<e → ∀ x : Cross a, ‖x‖ ≤ (t:ℝ) → tension x t p ≤ 0) (x : Cross a) (hx : ‖x‖ ≤ 1) :
    (inner ℝ (SEP a p) x)^2 ≤ (p a)^2 := by
  let q:= inner ℝ (SEP a p) x
  let d := fun t:ℝ => exp (-(p a)*t)
  let f(t:ℝ):ℝ:= 2 * Real.sin (t*(q/2))*d t; let g(t:ℝ):ℝ:=1-d t
  have e₀ : d 0=1:= by simp [d];
  have f₀ : f 0=0:= by simp [f]
  have g₀ : g 0=0:= by simp [g,e₀]
  have hd : HasDerivAt d (-(p a)) 0 := by simpa [d] using (((hasDerivAt_id' (0:ℝ)).const_mul (-(p a))).exp)
  have hf : HasDerivAt f q 0 := by
    convert ((((hasDerivAt_id' (0:ℝ)).mul_const (q/2)).sin.const_mul 2).mul hd) using 1 <;> try rfl
    simp [e₀]; ring
  have hg : HasDerivAt g (p a) 0 := by simpa [g] using (hd.const_sub 1)
  apply le_of_tendsto_of_tendsto (hf.tendsto_slope_zero_right.pow 2) (hg.tendsto_slope_zero_right.pow 2)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds b)] with t v ht
  change (t⁻¹ • (f (0+t) - f 0))^2 ≤(t⁻¹ • (g (0+t)-g 0))^2
  simp only [f₀,g₀,sub_zero,smul_eq_mul,mul_pow,zero_add]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  let bt : 0 < t := v
  have H₁:=he ⟨t,bt.le⟩ (show 0<(⟨t,bt.le⟩:ℝ≥0) from bt) ht (t • x) (by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg bt.le]; exact mul_le_of_le_one_right bt.le hx)
  erw [trig_rel, sub_nonpos, real_inner_smul_right (SEP a p) x t] at H₁
  dsimp only [f,g,d,q]; rw [← mul_div_assoc]; exact H₁

/-- Forward cone from paying this stamp budget on this physical space. -/
theorem prices_spectrum {e : ℝ} (p : 0 < e) (h : Cools S e) : Forward S := by
  ext1 v
  apply ((P).null_pair (closed_front a).isOpen_compl.measurableSet v).mp
  refine measure_mono_null (compl_subset_compl.mpr ?_) measure_compl_support
  intro x H₁
  let k : Cross a := SEP a x; change ‖k‖≤ x a
  have t : 0 ≤ x a := S.nonneg v H₁
  have e := surf e x p t (fun t p v' y b=> tension_point S y t (h t p v' y b) v x H₁)
  by_cases z : ‖k‖=0; · simpa [z]
  have H₂ := e (‖k‖⁻¹ • k) (by rw [norm_smul,norm_inv,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ z]); change (inner ℝ k _)^2 ≤_ at H₂
  erw [real_inner_smul_right k k,real_inner_self_eq_norm_sq,pow_two (‖k‖), ← mul_assoc, inv_mul_cancel₀ z,one_mul] at H₂
  exact (sq_le_sq₀ (norm_nonneg _) t).mp H₂

theorem true_spectrum_price {e : ℝ} (p : 0 < e) : Forward S ↔ Cools S e := ⟨fun h _ _ _ _ v i => tension_bill S i v h, prices_spectrum S p⟩
end location
end YM.ConePrice

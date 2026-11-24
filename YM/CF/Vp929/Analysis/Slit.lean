import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Propagation from the slit

The geometry from VOLUME_RATE, normalized parameter τ/R. Slightly different absolute constants:
we work directly on circular annuli in `w`, using |w| = 7 instead of up to the |z| = 1/2 boundary
of the slit domain. That outer circle too maps to |z| ≤ 1/2. Use a vertical strip via `w=exp u`.
-/
set_option autoImplicit false
noncomputable section
open Complex Complex.HadamardThreeLines Set Filter Function Topology Metric
namespace YM.CF.VolumeRate

/-- Uniform propagation fraction. -/
def propagation : ℝ := 1 - Real.log 4 / Real.log 7
lemma propagation_pos : 0 < propagation := sub_pos.mpr ((div_lt_one (Real.log_pos (by norm_num))).2 (Real.log_lt_log (by norm_num) (by norm_num)))
lemma propagation_le_one : propagation ≤ 1 := sub_le_self _ (by positivity)

private def slitMap (z : ℂ) := (exp z + (exp z)⁻¹) / 16
private lemma slitMap_mem {z : ℂ} (hz : z ∈ verticalClosedStrip 0 (Real.log 7)) :
    slitMap z ∈ ball 0 1 := by
  rw [mem_ball_zero_iff, slitMap, norm_div]
  have h₁ : 1 ≤ ‖exp z‖ := by rw [norm_exp]; exact Real.one_le_exp hz.1
  have h₂ : ‖exp z‖ ≤ 7 := by
    rw [norm_exp]; exact (Real.exp_monotone hz.2).trans_eq (Real.exp_log (by norm_num))
  have := (norm_add_le (exp z) (exp z)⁻¹).trans <|
    add_le_add h₂ (by simpa [one_div] using (one_div_le_one_div_of_le (by norm_num) h₁) : ‖(exp z)⁻¹‖ ≤ 1/1)
  norm_num at *
  linarith

private lemma slitMap_w {x : ℝ} (hx : x ∈ Icc (1/8 : ℝ) (1/4)) :
    ∃ w : ℝ, 1 ≤ w ∧ w ≤ 4 ∧ ((w : ℂ) + (w : ℂ)⁻¹)/16 = x := by
  rcases hx with ⟨h1,h2⟩
  let a := 8*x
  change 1/8 ≤ x at h1
  change x ≤ 1/4 at h2
  have hA : 1 ≤ a := by dsimp [a]; linarith
  have hB : a ≤ 2 := by dsimp [a]; linarith
  let b := Real.sqrt (a^2-1); have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hd : b^2 = a^2-1 := Real.sq_sqrt (by nlinarith)
  have e : 0 < a+b := by linarith
  refine ⟨a+b, by linarith, by nlinarith, ?_⟩
  norm_cast
  field_simp
  dsimp [a] at *
  nlinarith

private lemma slitMap_pre {x : ℝ} (hx : |x| ∈ Icc (1/8 : ℝ) (1/4)) :
    ∃ z ∈ verticalClosedStrip 0 (Real.log 7), z.re ≤ Real.log 4 ∧ slitMap z = x := by
  obtain ⟨w,A,B,h⟩ := slitMap_w hx
  have e : w ≠ 0 := ne_of_gt (by linarith)
  have L : Real.log w ∈ Icc 0 (Real.log 7) := ⟨Real.log_nonneg A, Real.log_le_log (by linarith) (by linarith)⟩
  have L' : Real.log w ≤ Real.log 4 := Real.log_le_log (by linarith) B
  rcases le_total 0 x with v|v
  · refine ⟨log (w:ℂ), ?_, ?_, ?_⟩
    all_goals try simp only [verticalClosedStrip, mem_preimage, log_re, norm_real, Real.norm_eq_abs,
              abs_of_nonneg (show 0 ≤ w by linarith)]
    · exact L
    · exact L'
    · simpa [slitMap, Complex.exp_log (ofReal_ne_zero.mpr e), abs_of_nonneg v] using h
  · refine ⟨log (- (w:ℂ)), ?_, ?_, ?_⟩
    all_goals try simp only [verticalClosedStrip, mem_preimage, log_re, norm_neg, norm_real, Real.norm_eq_abs,
              abs_of_nonneg (show 0 ≤ w by linarith)]
    · exact L
    · exact L'
    · rw [slitMap, exp_log (neg_ne_zero.mpr (ofReal_ne_zero.mpr e)), inv_neg, ←neg_add, neg_div, h, abs_of_nonpos v, ofReal_neg, neg_neg]

/-- Slit-to-circle logarithmic propagation (estimate on the widened real segment that it buys). -/
theorem slit_propagation {f : ℂ → ℂ} {M a : ℝ} (haM : a ≤ M)
    (h : DifferentiableOn ℂ f (ball 0 1)) (hu : ∀ z ∈ ball (0:ℂ) 1, ‖f z‖ ≤ Real.exp M)
    (hs : ∀ x : ℝ, |x| ≤ 1/8 → ‖f x‖ ≤ Real.exp a)
    (x : ℝ) (hx : |x| ≤ 1/4) : ‖f x‖ ≤ Real.exp (M - propagation * (M-a)) := by
  by_cases h₀ : |x| ≤ 1/8
  · exact (hs x h₀).trans (Real.exp_monotone (by nlinarith [propagation_le_one]))
  obtain ⟨z,hz,hz',e⟩ := slitMap_pre ⟨(le_of_not_ge h₀), hx⟩
  let g := f ∘ slitMap
  have q : (0:ℝ) < Real.log 7 := Real.log_pos (by norm_num)
  have hg (z) (p : z ∈ verticalClosedStrip 0 (Real.log 7)) : ‖g z‖ ≤ Real.exp M := hu _ (slitMap_mem p)
  have hd : DifferentiableOn ℂ g (verticalClosedStrip 0 (Real.log 7)) := h.comp
    (Differentiable.differentiableOn (show Differentiable ℂ slitMap from
       (((Complex.differentiable_exp).add ((Complex.differentiable_exp).inv exp_ne_zero)).div_const _)))
    fun _ p=> slitMap_mem p
  have hb : BddAbove ((norm ∘ g) '' verticalClosedStrip 0 (Real.log 7)) := ⟨_, forall_mem_image.mpr hg⟩
  have hg' (w) (p : w ∈ re ⁻¹' {(0:ℝ)}) : ‖g w‖ ≤ Real.exp a := by
    have h : ‖exp w‖ = 1 := by rw [norm_exp, show w.re = 0 from p, Real.exp_zero]
    have e : slitMap w = (((exp w).re / 8 : ℝ) : ℂ) := by
      rw [slitMap, inv_eq_conj h, add_conj]
      push_cast; ring
    change ‖f _‖ ≤ _
    rw [e]
    apply hs
    rw [abs_div]; gcongr
    · exact (abs_re_le_norm _).trans_eq h
    · norm_num
  let t := z.re / Real.log 7
  have hc : closure (verticalStrip 0 (Real.log 7)) ⊆ verticalClosedStrip 0 (Real.log 7) :=
    closure_minimal (preimage_mono Ioo_subset_Icc_self) (isClosed_Icc.preimage Complex.continuous_re)
  have hf := norm_le_interp_of_mem_verticalClosedStrip' q hz
    ⟨hd.mono (preimage_mono Ioo_subset_Icc_self), hd.continuousOn.mono hc⟩ hb hg'
    (fun w hw => hg w (by change w.re ∈ Icc 0 (Real.log 7); rw [show w.re = Real.log 7 from hw]; exact right_mem_Icc.mpr q.le))
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, sub_zero, sub_zero] at hf
  change ‖f (slitMap z)‖ ≤ _ at hf; rw [e] at hf; refine hf.trans (Real.exp_monotone ?_)
  have hv : z.re / Real.log 7 ≤ Real.log 4 / Real.log 7 := by gcongr
  unfold propagation; nlinarith

end YM.CF.VolumeRate

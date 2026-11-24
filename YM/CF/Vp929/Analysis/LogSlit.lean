import YM.CF.Vp929.Analysis.Slit
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.CanonicalDecomposition
/-!
# Integral bound

Use Jensen's zero-removal argument. Count and cost zeros in one induction, on steps of log(3/2)
in the center's log budget. Each zero in the concentric closed radius 1/2 ball is removed by
dividing out a radius 3/4 Blaschke factor; thus the outer circle is unchanged in absolute value
while we decrease the center budget. This avoids needing to find circles without zeros. Once ready,
log loss is nonnegative harmonic on the small ball, and use Poisson to pay Harnack.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.VolumeRate
open Complex ComplexConjugate Function Set Filter Topology Metric MeasureTheory InnerProductSpace

private lemma harnack {c z : ℂ} {f : ℂ → ℝ} (p : HarmonicOnNhd f (closedBall c (1/2)))
    (h : ∀ x ∈ sphere c (1/2), 0 ≤ f x) (q : ‖z-c‖ ≤ 1/4) : f z ≤ 4*f c := by
  have hd (x) (hx : x ∈ sphere c (1/2)) : 1/4 ≤ ‖(x-c)-(z-c)‖ :=
    le_trans (by rw [mem_sphere_iff_norm] at hx; linarith : 1/4 ≤ ‖x-c‖ - ‖z-c‖) (norm_sub_norm_le ..)
  have hg : ContinuousOn f (sphere c (1/2)) := fun x hx=> (p x (sphere_subset_closedBall hx)).1.continuousAt.continuousWithinAt
  have hv : z ∈ ball c (1/2) := mem_ball_iff_norm.mpr (by linarith)
  have e : (|(1/2:ℝ)|) = 1/2 := by norm_num
  calc
    f z = _ := (p.circleAverage_poissonKernel_smul hv).symm
    _ ≤ Real.circleAverage ((4:ℝ) • f) c (1/2) := by
      apply Real.circleAverage_mono
      · apply ContinuousOn.circleIntegrable'
        rw [e]; refine ContinuousOn.smul ?_ hg
        intro x hx; refine ContinuousAt.continuousWithinAt ?_
        have h : ‖(x-c) - (z-c)‖^2 ≠ 0 := pow_ne_zero _ (ne_of_gt (by linarith [hd x hx]))
        unfold poissonKernel; fun_prop
      · apply ContinuousOn.circleIntegrable'
        rw [e]; exact continuousOn_const.smul hg
      · rw [e]; intro x hx; have H:= hd x hx
        apply mul_le_mul_of_nonneg_right _ (h _ hx)
        rw [poissonKernel_def]; apply (div_le_iff₀ (by positivity : 0 < ‖(x-c)-(z-c)‖^2)).2
        rw [mem_sphere_iff_norm] at hx; rw [hx]; nlinarith
    _ = 4*f c := by rw [Real.circleAverage_smul, HarmonicOnNhd.circleAverage_eq (by rwa [e])]; rfl

/-- Divide out one Blaschke factor, preserving the upper bound. -/
private lemma remove_one {c w : ℂ} {f : ℂ → ℂ} {M : ℝ} (hf : DifferentiableOn ℂ f (closedBall c (3/4)))
    (hm : ∀ x ∈ closedBall c (3/4), ‖f x‖ ≤ M) (hw : w ∈ closedBall c (1/2)) (he : f w=0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (closedBall c (3/4)) ∧ (∀ x ∈ closedBall c (3/4), ‖g x‖ ≤ M) ∧
      ∀ x, x ≠ w → g x = f x * canonicalFactor (3/4) (w-c) (x-c) := by
  let R : ℝ := 3/4
  let g := fun x => dslope f w x * (((R:ℂ)^2-conj (w-c)*(x-c))/R)
  have hw' : w ∈ ball c R := closedBall_subset_ball (by dsimp [R]; norm_num) hw
  have hg : DifferentiableOn ℂ g (closedBall c R) :=
    ((differentiableOn_dslope (mem_of_superset (isOpen_ball.mem_nhds hw') ball_subset_closedBall)).2 hf).mul
    (Differentiable.differentiableOn (by fun_prop))
  have hr {x : ℂ} (h : x ≠ w) : g x = f x * canonicalFactor R (w-c) (x-c) := by
    simp only [g, canonicalFactor_apply, dslope_of_ne _ h, slope_def_field, he, sub_zero, sub_sub_sub_cancel_right]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  refine ⟨g,hg,?_,fun x h => hr h⟩
  intro x hx; apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball (hg.diffContOnCl_ball (Subset.refl _))
  · rw [frontier_ball c (by dsimp [R]; norm_num)]; intro y hy
    have hY : y ≠ w := by
      rw [mem_ball_iff_norm] at hw'; rw [mem_sphere_iff_norm] at hy; rintro rfl; linarith
    rw [hr hY, norm_mul, norm_canonicalFactor_eval_circle_eq_one ?wP ?zP, mul_one]
    case wP => exact mem_ball_zero_iff.mpr (mem_ball_iff_norm.mp hw')
    case zP => exact mem_sphere_zero_iff_norm.mpr (mem_sphere_iff_norm.mp hy)
    exact hm y (sphere_subset_closedBall hy)
  · rwa [closure_ball c (by dsimp [R]; norm_num)]

/-- Cost at the center of one zero. -/
private lemma factor_center {w : ℂ} (hw : ‖w‖ ≤ 1/2) (hz : w ≠ 0) :
    3/2 ≤ ‖canonicalFactor (3/4) w 0‖ := by
  have h : 0 < ‖w‖ := norm_pos_iff.mpr hz
  rw [canonicalFactor_apply, mul_zero, sub_zero, norm_div, norm_mul, norm_pow, norm_real,
    Real.norm_eq_abs, abs_of_pos (by norm_num), zero_sub, norm_neg]
  apply (le_div_iff₀ (by positivity)).2; nlinarith

private lemma test_size {c x : ℝ} (hc : |c| ≤ 1/8) (hx : |x| ≤ 1/8) :
    ‖(x : ℂ)-(c:ℂ)‖ ≤ 1/4 := by
  rw [← ofReal_sub, norm_real, Real.norm_eq_abs]; linarith [abs_sub x c]

/-- Cost at any evaluation; omit one point of the parameter interval. -/
private lemma factor_step {c x : ℝ} (hc : |c| ≤ 1/8) (hx : |x| ≤ 1/8) {w : ℂ}
    (hw : ‖w-c‖ ≤ 1/2) (he : x ≠ w.re) :
    Real.log ‖canonicalFactor (3/4) (w-(c:ℂ)) ((x:ℂ)-c)‖ ≤ Real.log 2 - Real.log (x - w.re) := by
  let v:= w-(c:ℂ); let y:ℂ:= (x:ℂ)-c; have hy : ‖y‖ ≤ 1/4 := test_size hc hx; have hv : ‖v‖ ≤ 1/2 := hw
  have ha : |x - w.re| ≤ ‖y-v‖ := by simpa [y,v] using (abs_re_le_norm ((x:ℂ)-w))
  have hτ: 0 < |x - w.re| := abs_pos.mpr (sub_ne_zero.mpr he)
  have hk: 0 < ‖y-v‖ := hτ.trans_le ha
  let A:= canonicalFactor (3/4) v y; let R:ℝ:=3/4; change Real.log ‖A‖ ≤ _
  rw [←Real.log_abs (x-w.re), ← Real.log_div (by norm_num) hτ.ne']
  apply Real.log_le_log (norm_pos_iff.mpr (canonicalFactor_ne_zero (mem_ball_zero_iff.mpr (by linarith))
      (mem_closedBall_zero_iff.mpr (by linarith)) (sub_ne_zero.mp (norm_pos_iff.mp hk))))
  rw [canonicalFactor_apply R v y, norm_div,norm_mul,norm_real,Real.norm_eq_abs, abs_of_pos (by dsimp [R]; norm_num : 0<R)]
  calc
    _ ≤ (2*R)/(R*|x-w.re|) := by
      gcongr
      · exact (norm_sub_le ..).trans <| by rw [norm_pow,norm_mul,norm_conj,norm_real,Real.norm_eq_abs]; unfold R; rw [abs_of_pos (by norm_num)]; nlinarith [norm_nonneg y,norm_nonneg v]
    _ = 2/|x-w.re| := by field_simp [show R ≠ 0 by unfold R; norm_num]

abbrev choiceMeasure : Measure ℝ := volume.restrict (Ioc 0 (1/8:ℝ))
abbrev loss (M : ℝ) (f : ℂ → ℂ) (x : ℝ) := M - Real.log ‖f x‖

private lemma loss_integrable {c M : ℝ} (hc : |c| ≤ 1/8) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (closedBall (c:ℂ) (3/4))) : Integrable (loss M f) choiceMeasure := by
  refine Integrable.sub (integrable_const M) (MeromorphicOn.intervalIntegrable_log_norm
              (show MeromorphicOn (fun x:ℝ=> f (x:ℂ)) (uIcc (0:ℝ) (1/8)) from ?_)).1
  intro x hx; have H : |x| ≤ 1/8 := by rw [uIcc_of_le (by norm_num)] at hx; simpa [abs_of_nonneg hx.1] using hx.2
  apply AnalyticAt.meromorphicAt
  have h : (x:ℂ) ∈ ball (c:ℂ) (3/4) := mem_ball_iff_norm.mpr (lt_of_le_of_lt (test_size hc H) (by norm_num))
  exact ((((hf.mono ball_subset_closedBall).analyticOnNhd isOpen_ball) _ h).restrictScalars).comp (ofRealCLM.analyticAt _)

private lemma step_integral_aux (w : ℝ) : Integrable (fun x=> -Real.log (x-w)) (volume.restrict (Ioc (w-1) (w+1))) :=
  (.neg (MeromorphicOn.intervalIntegrable_log (f := fun x=> x-w) (by intro; fun_prop)).1)
private lemma step_le_aux {c : ℝ} (hc : |c| ≤ 1/8) (w : ℂ) (hw : ‖w-c‖ ≤ 1/2) :
    Ioc (0:ℝ) (1/8) ⊆ Ioc (w.re-1) (w.re+1) := by
  rw [abs_le] at hc; have h:= (abs_le.mp ((abs_re_le_norm (w-c)).trans hw)); simp only [sub_re,ofReal_re] at h
  rintro x ⟨x₁,x₂⟩; constructor <;> linarith [h.1,h.2,hc.1,hc.2]

private lemma step_integral (w : ℝ) :
    (∫ x in Ioc (w-1) (w+1), -Real.log (x-w)) = 2 := by
  rw [← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_neg,
      intervalIntegral.integral_comp_sub_right Real.log w, integral_log]
  ring_nf; simp
private lemma step_integral_le {c : ℝ} (hc : |c| ≤ 1/8) (w : ℂ) (hw : ‖w-c‖ ≤ 1/2) :
    (∫ x, -Real.log (x-w.re) ∂choiceMeasure) ≤ 2 := by
  rw [← step_integral w.re]; refine setIntegral_mono_set (step_integral_aux _) ?_ (Eventually.of_forall fun _ p => step_le_aux hc w hw p)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  change 0 ≤ -Real.log _
  obtain ⟨h₁,h₂⟩:= hx
  rw [←Real.log_abs]
  exact neg_nonneg.mpr (Real.log_nonpos (abs_nonneg _) (abs_le.mpr ⟨by linarith, by linarith⟩))

private lemma choice_mass : choiceMeasure.real univ = 1/8 := by
  simp [Measure.real,Real.volume_Ioc]

/-- Negative log integral and almost-everywhere nonvanishing. The price variable `k` pays
one unit per Blaschke factor and buys the Poisson step when removal stops. -/
private lemma price_log {c M : ℝ} (hc : |c| ≤ 1/8)
    (k : ℕ) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (closedBall (c:ℂ) (3/4)))
    (hu : ∀ z ∈ closedBall (c:ℂ) (3/4), ‖f z‖ ≤ Real.exp M)
    (hl : Real.exp (M - k*Real.log (3/2)) ≤ ‖f c‖) :
    (∀ᵐ x : ℝ ∂choiceMeasure, f x ≠ 0) ∧ (∫ x, loss M f x ∂choiceMeasure) ≤ 4*k := by
  by_cases H : ∀ z ∈ closedBall (c:ℂ) (1/2), f z ≠ 0
  · have h (x : ℝ) (h : x ∈ Ioc 0 (1/8 : ℝ)) := test_size hc (x:=x) ((abs_of_pos h.1).trans_le h.2)
    have p:= closedBall_subset_ball (x:=(c:ℂ)) (by norm_num : (1/2:ℝ)<3/4)
    let G (z:ℂ) := M-Real.log ‖f z‖
    have A : HarmonicOnNhd G (closedBall (c:ℂ) (1/2)) := fun x hx =>
      (harmonicAt_const M).sub (((hf.mono ball_subset_closedBall).analyticOnNhd isOpen_ball x (p hx)).harmonicAt_log_norm (H x hx))
    have P (x : ℂ) (t : x ∈ sphere (c:ℂ) (1/2)) : 0 ≤ G x := sub_nonneg.mpr ((Real.log_le_log
      (norm_pos_iff.mpr (H x (sphere_subset_closedBall t))) (hu x (ball_subset_closedBall (p (sphere_subset_closedBall t))))).trans_eq (Real.log_exp _))
    have B : Real.log (Real.exp (M - k*Real.log (3/2))) ≤ Real.log ‖f (c:ℂ)‖ := Real.log_le_log (Real.exp_pos _) hl
    rw [Real.log_exp] at B
    constructor
    · filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioc] with x hx
      exact H _ (mem_closedBall_iff_norm.mpr ((h _ hx).trans (by norm_num)))
    calc
      _ ≤ ∫ _, 4*(k*Real.log (3/2)) ∂choiceMeasure := integral_mono_ae (loss_integrable hc hf) (integrable_const _) <| by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        exact le_trans (harnack A P (h _ hx)) (by dsimp [G]; linarith)
      _ ≤ _ := by rw [integral_const, choice_mass, smul_eq_mul]; nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3/2)]
  push Not at H
  obtain ⟨w,hw,h⟩:= H
  obtain ⟨g,hg,hU,E⟩:= remove_one hf hu hw h
  have hW : ‖w-c‖ ≤ 1/2 := mem_closedBall_iff_norm.mp hw
  have hfc : f c ≠ 0 := norm_pos_iff.mp ((Real.exp_pos _).trans_le hl)
  have hcw : w ≠ c := fun e=> hfc (e ▸ h)
  have hL := factor_center hW (sub_ne_zero.mpr hcw)
  let δ:= Real.log (3/2); have hδ : 0 < δ := Real.log_pos (by norm_num)
  have h₁ : Real.exp (M-k*δ+δ) ≤ ‖g c‖ := by
    rw [Real.exp_add, E _ hcw.symm, norm_mul, sub_self, Real.exp_log (by norm_num : (0:ℝ)<3/2)]
    gcongr
  cases k with
  | zero => have H := h₁.trans (hU c (mem_closedBall_self (by norm_num))); rw [Real.exp_le_exp] at H; push_cast at H; linarith
  | succ k =>
    obtain ⟨x,v⟩:= price_log hc k g hg hU (show Real.exp (M-k*δ) ≤ ‖g c‖ from le_trans (Real.exp_monotone (by push_cast; linarith)) h₁)
    have h' : ∀ᵐ x : ℝ ∂choiceMeasure, x ≠ w.re := choiceMeasure.ae_ne _
    have e : ∀ x:ℝ, x ≠ w.re → (x:ℂ) ≠ w := fun x h A => h (congrArg Complex.re A)
    have hf': ∀ᵐ x : ℝ ∂choiceMeasure, f x ≠ 0 ∧ canonicalFactor (3/4) (w-(c:ℂ)) ((x:ℂ)-c) ≠ 0 := by
      filter_upwards [h',x] with x h A; rwa [E _ (e x h), mul_ne_zero_iff] at A
    refine ⟨hf'.mono (fun x h=> h.1),?_⟩
    have T : Integrable (fun x=> -Real.log (x-w.re)) choiceMeasure := (step_integral_aux _).mono_measure (Measure.restrict_mono' (Eventually.of_forall fun x h => step_le_aux hc w hW h) le_rfl)
    calc
      _ ≤ ∫ x, loss M g x + (Real.log 2 + -Real.log (x-w.re)) ∂choiceMeasure := integral_mono_ae
          (loss_integrable hc hf) ((loss_integrable hc hg).add ((integrable_const _).add T)) <| by
        filter_upwards [h', hf', ae_restrict_mem measurableSet_Ioc] with x h hx hx'
        have h₂:= factor_step hc ((abs_of_pos hx'.1).trans_le hx'.2) hW h
        unfold loss; rw [E _ (e x h),norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hx.1) (norm_ne_zero_iff.mpr hx.2)]
        linarith
      _ ≤ _ := by
        have τ := step_integral_le hc w hW
        rw [integral_add (loss_integrable hc hg) (show Integrable (fun x=>Real.log 2 + -Real.log (x-w.re)) choiceMeasure from (integrable_const _).add T), integral_add (integrable_const _) T,
            integral_const, choice_mass, smul_eq_mul]; push_cast
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
termination_by k

/-- Jensen-Blaschke integral estimate near the rescaled segment with a paid point. -/
theorem integral_loss {c M a : ℝ} (hc : |c| ≤ 1/8)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (closedBall (c:ℂ) (3/4)))
    (hu : ∀ z ∈ closedBall (c:ℂ) (3/4), ‖f z‖ ≤ Real.exp M)
    (hl : Real.exp a ≤ ‖f c‖) :
    (∀ᵐ x : ℝ ∂choiceMeasure, f x ≠ 0 ∧ 0 ≤ loss M f x) ∧ Integrable (loss M f) choiceMeasure ∧
    (∫ x, loss M f x ∂choiceMeasure) ≤ 4*((M-a)/ Real.log (3/2) + 1) := by
  let s := Real.log (3/2); have h : 0 < s := Real.log_pos (by norm_num)
  have he:= hl.trans (hu c (mem_closedBall_self (by norm_num))); rw [Real.exp_le_exp] at he
  let b := (M-a)/s; let n:= ⌈b⌉₊; have t:= Nat.le_ceil b
  have hT : b ≤ n := t; have e: M-(n:ℝ)*s ≤ a := by linarith [(div_le_iff₀ h).1 hT]
  obtain ⟨H,W⟩:= price_log hc n f hf hu (le_trans (Real.exp_monotone e) hl)
  refine ⟨?_, loss_integrable hc hf, W.trans ?_⟩
  · filter_upwards [H,ae_restrict_mem measurableSet_Ioc] with x hx hx'; refine ⟨hx,sub_nonneg.mpr ?_⟩
    exact (Real.log_le_log (norm_pos_iff.mpr hx) (hu _ (mem_closedBall_iff_norm.mpr
          ((test_size hc ((abs_of_pos hx'.1).trans_le hx'.2)).trans (by norm_num))))).trans_eq (Real.log_exp _)
  gcongr; exact (Nat.ceil_lt_add_one (by unfold b; exact div_nonneg (sub_nonneg.mpr he) h.le)).le
end YM.CF.VolumeRate

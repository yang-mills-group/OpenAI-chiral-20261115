import Zephyr.Chern.Piola
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice Silk YM.Laurent MeasureTheory


-- probability measure, normalized periods
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : Measure.IsOpenPosMeasure (globe Axis) :=
  inferInstanceAs (Measure.IsOpenPosMeasure volume)

private lemma integral_peak {f g : Brill → ℝ}
    (fc : Continuous f) (gc : Continuous g)
    (af : 0 ≤ f) (hf : f 0=2) (uf : ∀ t,t≠0 → f t<2)
    (hg : 0<g 0) :
    ∃ n : ℕ, 0 < ∫ t, (f t)^n*g t ∂globe Axis := by
  obtain ⟨K,k,k',fk⟩ : ∃ K : ℝ,0<K ∧ K<2 ∧ ∀ t,g t ≤ 0 → f t ≤ K := by
    by_cases h : {t | g t ≤ 0}.Nonempty
    · obtain ⟨v,(hv : g v ≤ 0),hmax⟩ := (isClosed_le gc continuous_const).isCompact.exists_isMaxOn h fc.continuousOn
      exact ⟨max 1 (f v),lt_max_of_lt_left zero_lt_one, max_lt (by norm_num) (uf v (by rintro rfl;linarith)),
        fun t ht => le_max_of_le_right (hmax ht)⟩
    exact ⟨1,zero_lt_one,by norm_num,fun t ht => (h ⟨t,ht⟩).elim⟩
  let u t := f t/K
  let v t := max (u t - 1) 0 * max (g t) 0

  have u0 t : 0 ≤ u t := div_nonneg (af t) k.le
  have vc : Continuous v := by unfold v u;fun_prop
  have integ {r : Brill → ℝ} (hc : Continuous r) : Integrable r (globe Axis) :=
    hc.integrable_of_hasCompactSupport (.of_compactSpace _)
  have hp : 0< v 0 := by
    have o : 0< u 0 - 1 := sub_pos.mpr ((one_lt_div k).mpr (by rwa [hf]))
    exact mul_pos (lt_max_of_lt_left o) (lt_max_of_lt_left hg)
  have hi := integral_pos_of_integrable_nonneg_nonzero vc (integ vc)
    (fun _ => mul_nonneg (le_max_right ..) (le_max_right ..)) hp.ne'
  obtain ⟨C,b⟩ := isCompact_univ.exists_bound_of_continuousOn gc.continuousOn
  have C0 := (norm_nonneg _).trans (b 0 (Set.mem_univ _))
  obtain ⟨n,hn⟩ := exists_nat_gt (C / (∫ t, v t ∂globe Axis))
  have bd (t) : (n:ℝ)*v t - C ≤ (u t)^n * g t := by
    by_cases neg : g t ≤ 0
    · have uu : u t ≤ 1 := (div_le_one k).mpr (fk t neg)
      have v0 : v t=0 := by unfold v;rw [max_eq_right neg,mul_zero]
      rw [v0,mul_zero,zero_sub]
      apply le_trans _ (mul_le_mul_of_nonpos_right (pow_le_one₀ (u0 t) uu) neg)
      rw [one_mul, neg_le]
      exact (neg_le_abs _).trans (by simpa only [Real.norm_eq_abs] using b t (Set.mem_univ _))
    have g0 := (lt_of_not_ge neg).le

    apply (sub_le_self _ C0).trans
    unfold v
    rw [max_eq_left g0,←mul_assoc]
    apply mul_le_mul_of_nonneg_right _ g0
    by_cases h : u t ≤ 1
    · rw [max_eq_right (sub_nonpos.mpr h), mul_zero]; exact pow_nonneg (u0 t) _
    have e:= one_add_mul_le_pow (a:=u t-1) (by linarith) n
    rw [max_eq_left (by linarith)]
    rw [show 1+(u t-1)=u t by ring] at e
    linarith
  have w := (integ vc).const_mul (n:ℝ)
  have e := integral_mono (w.sub (integrable_const C))
    (integ (r:=fun t => (u t)^n*g t) (by unfold u;fun_prop)) bd
  simp only [Pi.sub_apply] at e
  rw [integral_sub w (integrable_const _), integral_const_mul, integral_const,
    probReal_univ,one_smul] at e
  use n
  rw [show f=(fun t => K*u t) by funext t; exact (mul_div_cancel₀ _ k.ne').symm]
  simp_rw [mul_pow,mul_assoc,integral_const_mul]
  exact mul_pos (pow_pos k _) ((sub_pos.mpr ((div_lt_iff₀ hi).mp hn)).trans_le e)

/-- Elementary polar conditions, for the pole at momentum zero. -/
structure Polar (f : Streams) : Prop where
  sphere : Sphere f
  peak : E 0 (f 0)=1
  real (t) : (E t (f 0)).im=0
  bottom (t) : -1 ≤ (E t (f 0)).re
  avoid (t) : t≠0 → (E t (f 0)).re<1
  facing : 0<(E 0 (jac f)).re

variable {f : Streams}
theorem Polar.price (h : Polar f) : 0<(τ (jac f)).re := by
  let a(t) := 1+(E t (f 0)).re
  have ac : Continuous a := continuous_const.add (Complex.continuous_re.comp (f 0).E_cont)
  have ic : Continuous (fun t => (E t (jac f)).re) := (Complex.continuous_re.comp (jac f).E_cont)
  obtain ⟨n,hn⟩ := integral_peak ac ic
    (fun t => by change 0≤1+(E t _).re; linarith [h.bottom t])
    (by unfold a;rw [h.peak];norm_num)
    (fun t w => by unfold a; linarith [h.avoid t w]) h.facing
  have e t : E t (1+f 0)=(a t:ℂ) := by
    unfold a
    simp only [map_add,map_one, Complex.ofReal_add,Complex.ofReal_one]
    congr 1
    apply Complex.ext <;> simp [h.real t]
  have pk : 0 < (moment f n).re := by
    rw [moment, ←Silk.integral]
    change 0 < RCLike.re (∫ t,E t ((1+f 0)^n*jac f) ∂globe Axis)
    rw [←integral_re]
    · simp_rw [RCLike.re_to_complex,map_mul,map_pow,e,← Complex.ofReal_pow,Complex.re_ofReal_mul]; exact hn
    · exact (E_cont _).integrable_of_hasCompactSupport (.of_compactSpace _)
  clear hn
  induction n with
  | zero => simpa only [moment,pow_zero,one_mul] using pk
  | succ n ih =>
    have r := congrArg Complex.re (h.sphere.recur n)
    apply ih
    rw [Complex.mul_re,Complex.mul_re] at r
    simp at r
    by_contra w
    have p := mul_pos (by positivity : 0<(n:ℝ)+4) pk
    rw [r] at p
    exact p.not_ge (mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_gt w))

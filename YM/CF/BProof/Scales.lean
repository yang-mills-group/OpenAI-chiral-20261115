import YM.Pressure.Seeds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Scales in the B expansion

Monomial in powers of y, s_y=exp((log log y)^2), log y (defined via exp even outside
the admitted range, to keep the power arithmetic exact). This hierarchy will be convenient
for proving bounds uniform in y (PL maps and NPL prices). Real argument to all these scales
is y already; thresholds on y can be required when picking x by monotonicity y≥x.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof
open Pressure Filter Set
open Real (exp log)
open scoped Topology

def coin (y a b c : ℝ) := exp (log y*a+(log (log y))^2*b + log (log y)*c)
abbrev g (y : ℝ) := coin y (-1/2) 0 0
abbrev scaleY (y : ℝ) := coin y 0 1 0
abbrev thresh (y : ℝ) := coin y (-1/2) 1 0
abbrev mA (y : ℝ) := coin y (-1/2) (3/4) 0
abbrev aA (y : ℝ) := coin y (-1/4) (3/8) 0
abbrev wc (y : ℝ) := coin y (-1/2) (1/2) 0
abbrev xi (y : ℝ) := coin y (-3/2) 0 0
abbrev allowance (y : ℝ) := coin y 0 (-1/8) 0 -- sigmaN

@[simp] lemma coin_pos (y a b c : ℝ) : 0<coin y a b c := Real.exp_pos _
@[simp] lemma coin_zero (y : ℝ) : coin y 0 0 0=1 := by simp [coin]
lemma coinY {y : ℝ} (h : 0<y) : coin y 1 0 0=y := by simp [coin,Real.exp_log h]
lemma coinLog {y : ℝ} (h : 1<y) : coin y 0 0 1=log y := by simp [coin,Real.exp_log (Real.log_pos h)]
lemma coin_scale (y : ℝ) : scaleY y=exp (log (log y)^2) := by simp [coin]
lemma coin_mul (y a b c d e f : ℝ) : coin y a b c*coin y d e f=coin y (a+d) (b+e) (c+f) := by unfold coin; rw [← Real.exp_add]; ring_nf
lemma coin_inv (y a b c : ℝ) : (coin y a b c)⁻¹=coin y (-a) (-b) (-c) := by unfold coin; rw [← Real.exp_neg]; ring_nf
lemma coin_div (y a b c d e f : ℝ) : coin y a b c/coin y d e f=coin y (a-d) (b-e) (c-f) := by simp only [div_eq_mul_inv,coin_inv,coin_mul,sub_eq_add_neg]
lemma coin_rpow (y a b c d : ℝ) : coin y a b c ^ d = coin y (a*d) (b*d) (c*d) := by unfold coin; rw [← Real.exp_mul]; ring_nf
lemma coin_pow (y a b c : ℝ) (d : ℕ) : coin y a b c ^ d=coin y (a*d) (b*d) (c*d) := by rw [← Real.rpow_natCast, coin_rpow]
lemma thresh_eq {y : ℝ} (h : 0<y) : thresh y=temp y := by
 unfold temp
 rw [← coin_scale,Real.sqrt_eq_rpow]; nth_rw 2 [← coinY h]
 rw [coin_rpow,coin_inv,coin_mul]; unfold thresh; ring_nf

lemma coin_purchases {a b c : ℝ} (h : a < 0 ∨ a=0 ∧ b<0 ∨ a=0 ∧ b=0 ∧ c<0) :
    Tendsto (fun y=> coin y a b c) atTop (𝓝 0) := by
 apply Real.tendsto_exp_atBot.comp (f:=fun y=>log y*a+(log (log y))^2*b+log (log y)*c)
 let L(y:ℝ):= log (log y); let l(y:ℝ) := log y
 have he : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
 have ht : Tendsto l atTop atTop := Real.tendsto_log_atTop
 have hp : ∀ᶠ y:ℝ in atTop, 0 < l y := ht.eventually_gt_atTop 0
 change Tendsto (fun y=>l y*a+(L y)^2*b+L y*c) atTop atBot
 rcases h with h|⟨rfl,h⟩|⟨rfl,rfl,h⟩ -- rfl subst? a=0
 · have hi : Tendsto (fun y=> (L y)^2/l y) atTop (𝓝 0) := (Real.isLittleO_pow_log_id_atTop (n:=2)).tendsto_div_nhds_zero.comp ht
   have hq : Tendsto (fun y=> L y/l y) atTop (𝓝 0) := by simpa using! ((Real.isLittleO_pow_log_id_atTop (n:=1)).tendsto_div_nhds_zero.comp ht)
   have hu := (hi.mul_const b).add (hq.mul_const c); rw [zero_mul,zero_mul,add_zero] at hu
   apply tendsto_atBot_mono' _ _ (ht.atTop_mul_const_of_neg (r:=a/2) (by linarith))
   filter_upwards [hu.eventually (gt_mem_nhds (by linarith : 0 < -(a/2))),hp] with y hy hh
   change L y^2/l y*b+L y/l y*c < -(a/2) at hy; field_simp at hy; linarith
 · simp only [mul_zero,zero_add]; have hi : Tendsto (fun y => c/L y) atTop (𝓝 0):= by simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp he).const_mul c
   apply tendsto_atBot_mono' _ _ ((tendsto_pow_atTop (by decide : 2≠0) |>.comp he).atTop_mul_const_of_neg (r:=b/2) (by linarith))
   filter_upwards [hi.eventually (gt_mem_nhds (by linarith : 0 < -(b/2))),he.eventually_gt_atTop 0] with y hy hh
   change _ ≤ L y ^2*(b/2); have hv : c < -(b/2)*L y := (div_lt_iff₀ hh).mp hy; linarith [mul_lt_mul_of_pos_left hv hh]
 simp only [mul_zero,zero_add]; exact he.atTop_mul_const_of_neg h

lemma coin_budget {a b c d e f : ℝ} (h : a < d ∨ a=d ∧ b<e ∨ a=d∧ b=e∧ c<f) (C D : ℝ) (k : 0<D) :
    ∀ᶠ y:ℝ in atTop, C*coin y a b c < D*coin y d e f := by
 have hp:= (coin_purchases (a:=a-d) (b:=b-e) (c:=c-f) (by simpa only [sub_eq_zero,sub_neg] using h)).const_mul C
 rw [mul_zero] at hp
 filter_upwards [hp.eventually (gt_mem_nhds k)] with y hy
 refine (div_lt_iff₀ (coin_pos y d e f)).mp ?_
 rw [mul_div_assoc,coin_div]; exact hy
end YM.CF.BProof

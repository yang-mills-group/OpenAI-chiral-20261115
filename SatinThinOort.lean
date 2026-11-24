import YM.CF.BProof.Scales
import SatinThinLaplace
/-! # order control substantial: explicitly budget by real-scale account both sizes -/
set_option autoImplicit false
noncomputable section
namespace YM.Pressure.Worth
open Filter CF.BProof Asymptotics
open scoped Topology
abbrev Pays (a b c:ℝ)(f:ℝ→ℝ):Prop:= f=O[atTop] fun x:ℝ=> coin x a b c
abbrev Earlier (a b c w p q:ℝ):Prop:= a < w ∨ a=w ∧ b<p ∨ a=w∧ b=p∧ c<q
variable {f g e:ℝ→ℝ}{C k a b c w p q u v h:ℝ}
namespace Pays
lemma whole (a b c:ℝ) : Pays a b c (fun x=>coin x a b c):= isBigO_refl ..
lemma by_floor (h:∀ᶠ x in atTop, |f x| ≤ C*coin x a b c): Pays a b c f:= (isBigO_iff.mpr ⟨C,h.mono fun x hx=>by simpa only [Real.norm_eq_abs, abs_of_pos (coin_pos ..)] using hx⟩)
lemma constant (u:ℝ) : Pays 0 0 0 (fun _ :ℝ=> u):=by apply by_floor (C:=|u|); exact Eventually.of_forall fun i=> Eq.le (by rw [coin_zero,mul_one]);
lemma earn (k:Earlier a b c w p q): Pays w p q (fun x=> coin x a b c):=by
 apply by_floor (C:=1); filter_upwards [coin_budget k 1 1 zero_lt_one] with x hx; simpa only [one_mul, abs_of_pos (coin_pos ..)] using hx.le
lemma merit (t:Pays a b c f)(k:Earlier a b c w p q) : Pays w p q f:= t.trans (earn k)
lemma compare (g:ℝ) (s:0<g) (t:Pays a b c f) (k:Earlier a b c w p q): ∀ᶠ x:ℝ in atTop, |f x|≤g*coin x w p q:=by
 obtain ⟨u,t⟩:=isBigO_iff.mp t; filter_upwards [t,coin_budget k u g s] with x ht hy; exact le_trans (b:=u*coin x a b c) (by simpa only [Real.norm_eq_abs,abs_of_pos (coin_pos x ..)] using ht) hy.le
lemma leap (t:Pays a b c f)(k:Earlier a b c w p q): ∀ᶠ x:ℝ in atTop,f x≤ coin x w p q:=by simpa only [one_mul] using (compare 1 zero_lt_one t k).mono (fun x hx=>(le_abs_self _).trans hx)
lemma limit (t:Pays a b c f)(k:Earlier a b c 0 0 0): Tendsto f atTop (𝓝 0):= t.trans_tendsto (coin_purchases (by simpa only using k)) -- tune
lemma fix {a b c:ℝ} (t:Pays a b c f)(u:∀ᶠ x in atTop, f x=g x) : Pays a b c g:=by
 apply t.congr' u; rfl
lemma plus (t:Pays a b c f)(u:Pays a b c g): Pays a b c (fun x=> f x+g x):= t.add u
lemma minus (t:Pays a b c f)(u:Pays a b c g): Pays a b c (fun x=> f x-g x):= t.sub u
lemma times (t:Pays a b c f)(s:Pays w p q g): Pays (a+w) (b+p) (c+q) (fun x=> f x*g x):=by apply (t.mul s).congr _ fun x=> coin_mul x ..; intro x; rfl
lemma scale (C:ℝ)(t:Pays a b c f):Pays a b c (fun x=> C*f x):=  t.const_mul_left C
lemma right (C:ℝ)(t:Pays a b c f):Pays a b c (fun x=> f x*C):= by simp_rw [mul_comm (f _)]; exact scale C t
lemma pot (t:Pays a b c f)(n:ℕ) : Pays (a*n) (b*n) (c*n) (fun x=> f x^n):=by apply (t.pow n).congr _ (fun x=> coin_pow ..); intro x; rfl
lemma damp (a:ℝ)(t:0<a)(w p q:ℝ) : Pays w p q (fun x=> Real.exp (-(a* (radiusB x)))):=by
 -- exp -log² beats x^C
 apply merit (a:=w-1) (b:=0) (c:=0) _ (Or.inl (by linarith)); apply by_floor (C:=1)
 filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop ((1-w)/a),Real.tendsto_log_atTop.eventually_ge_atTop 0] with x hx e
 rw [one_mul, abs_of_pos (Real.exp_pos _),coin,mul_zero, mul_zero,add_zero,add_zero]; apply Real.exp_monotone; have h:= mul_le_mul_of_nonneg_left (show Real.log x ^ 2 ≤ (radiusB x:ℝ) from Nat.le_ceil _) t.le
 nlinarith only [h, mul_le_mul_of_nonneg_left ((div_le_iff₀ t).mp hx) e]
lemma rising : Pays 0 0 2 (fun x=> (radiusB x:ℝ)):=by
 apply by_floor (C:=2); filter_upwards [eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_gt_atTop 1] with x hx hz
 have he: Real.log x > 1:=hz; have hp:0≤ Real.log x:=by linarith
 have ht:(↑(radiusB x):ℝ) < Real.log x ^ 2 + 1:= Nat.ceil_lt_add_one (by positivity)
 rw [abs_of_nonneg (Nat.cast_nonneg _),show coin x 0 0 2=Real.log x^2 from ?_]; · nlinarith
 have hx':x>1:= Real.log_pos_iff (by linarith)|>.mp (by linarith)
 rw [← coinLog hx', coin_pow]; norm_num
lemma height : Pays 1 0 0 id:=by
 refine fix (whole 1 0 0) ((eventually_gt_atTop (0:ℝ)).mono (fun x hx=> coinY hx))
end Pays

-- Meter choices: cell power, external cut, pressure loss power(s). Inner allowance weight.
abbrev r_width : ℝ:=1/1000
abbrev r_shield : ℝ:=(-1/2)+(1/50)
abbrev r_meter :ℝ:= - (1/1250)
abbrev r_gate :ℝ:=1/125
abbrev widthC (x:ℝ):= coin x r_width 0 0
abbrev shieldC (x:ℝ):= coin x r_shield 0 0
abbrev meterC (x:ℝ):= coin x r_meter 0 0
abbrev gateC(x:ℝ):= coin x r_gate 0 0
lemma inner_shield : ∀ᶠ x:ℝ in atTop, temp x< shieldC x:=by
 filter_upwards [eventually_gt_atTop (0:ℝ),coin_budget (b:=1) (c:=0) (e:=0) (f:=0) (Or.inl (by norm_num [r_shield]: (-1/2:ℝ)<r_shield)) 1 1 zero_lt_one] with x hx hX
 rw [←thresh_eq hx]; simpa only [one_mul] using hX
end YM.Pressure.Worth

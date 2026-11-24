import YM.CF.Buffered.Duct
import YM.CF.Mint.Key
/-! Parameterizing gauge strips: width chosen ≳ log x and big enough for the
registered exponential path tail. Mesh radius pays thresholds (can overpay with
extra powers). This uses q≥ (log x)^4. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Alloy.Tariff
open Function NormedSpace Filter Finset Graph Lattice Laurent Wilson Analysis Pressure
open scoped Topology ContDiff InnerProductSpace BigOperators
open Mint Crust Crust.Grid
variable {a b c d K M:ℝ}
def shunt(x:ℝ):= Real.exp (-3*Real.log x)
lemma shunt_p(x:ℝ):0<shunt x:=Real.exp_pos _
lemma forerun : ∀ᶠ x:ℝ in atTop, shunt x ≤1∧ 16*shunt x ≤ temp x:= by
 let f(x:ℝ):= Real.log x
 filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 16, eventually_gt_atTop (0:ℝ)] with x hx v; change 16≤f x at hx
 let y:= f x; let t:= Real.exp (y/2); have he: t=Real.sqrt x:=by unfold t y f; rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos v]; congr 1; ring
 have ht:0<t:=Real.exp_pos _; have hw:= le_mul_of_one_le_right (inv_nonneg.mpr (show 0≤ Real.sqrt x from Real.sqrt_nonneg _)) (Real.one_le_exp (sq_nonneg (Real.log (Real.log x))))
 refine ⟨Real.exp_le_one_iff.mpr (by change -3*y≤0; change 16≤y at hx; linarith), le_trans ?_ hw⟩
 rw [←he]; change 16* Real.exp (-3*y)≤(Real.exp _)⁻¹; rw [← Real.exp_neg]; apply le_trans (mul_le_mul_of_nonneg_right (show 16 ≤ Real.exp y from ?_) (Real.exp_pos _).le); swap
 · change 16≤y at hx; linarith [Real.add_one_le_exp y]
 rw [←Real.exp_add]; exact Real.exp_le_exp.mpr (by change 16≤y at hx; linarith)

def spikes (a x:ℝ): ℕ:= Nat.ceil (4*Real.log x/a)+2
lemma spike_bounds (h:0<a)(g:1≤b): let n:ℝ:= spikes a b
 2 ≤ n ∧ 4*Real.log b/a ≤ n ∧ n ≤ 4*Real.log b/a+3:=by
 intro n; unfold n spikes; let x:= 4*Real.log b/a; have hx:0≤x:=by unfold x; have hg:=Real.log_nonneg g; positivity
 push_cast; exact ⟨by linarith only [show (0:ℝ)≤(Nat.ceil x:ℝ) by positivity,hx, Nat.le_ceil x],le_trans (Nat.le_ceil _) (by linarith),by linarith only [Nat.ceil_lt_add_one hx]⟩ -- inspect linarith x def
lemma echo_t : Tendsto (fun x:ℝ=> x*temp x^3) atTop (𝓝 0):=by
 let y(x:ℝ):= x ^ (-(1/8:ℝ))
 apply squeeze_zero' _ _ (tendsto_rpow_neg_atTop (show (0:ℝ)<1/8 by norm_num)); swap
 · filter_upwards [Work.E09.temp_cost (1/8) (by norm_num), eventually_gt_atTop (0:ℝ)] with x p e; let R:=-(1/2:ℝ)+1/8; apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Work.E09.temp_pos e).le p 3) e.le); apply le_of_eq; rw [← Real.rpow_natCast (_^R),←Real.rpow_mul e.le]; nth_rw 1 [←Real.rpow_one x]; rw [←Real.rpow_add e]; congr 1; norm_num
 filter_upwards [eventually_gt_atTop (0:ℝ)] with x p; apply mul_nonneg p.le (pow_nonneg (Work.E09.temp_pos p).le 3)
private lemma temp_zero : Tendsto temp atTop (𝓝 0):=by simpa using Work.E09.radiusB_temp 0
lemma uproot (C L:ℝ): Tendsto (fun x:ℝ=> x*(C*temp x^3+C*temp x^4)+L*temp x^2) atTop (𝓝 0):=by
 have he := ((echo_t.const_mul C).add ((echo_t.mul temp_zero).const_mul C)).add ((temp_zero.pow 2).const_mul L)
 simp only [mul_zero,add_zero,zero_pow (by decide : (2:ℕ)≠0)] at he; apply he.congr; intro x; ring
private lemma b₀ : ∀ᶠ x:ℝ in atTop,x*shunt x= x⁻¹ * x⁻¹:=by
 filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; unfold shunt; rw [neg_mul,Real.exp_neg,show Real.exp (3*Real.log x)=x^3 from ?_]; field_simp
 convert Real.exp_nat_mul (Real.log x) 3; simp; rw [Real.exp_log hx] -- tune
lemma ripple (h:0<a)(K:ℝ) : Tendsto (fun x:ℝ=> x*Crust.bend_cost (spikes a x) (2*shunt x) a c K) atTop (𝓝 0) := by
 have hx:= tendsto_inv_atTop_zero (𝕜:=ℝ); have ht:=Real.tendsto_log_atTop
 have he:Tendsto (fun x:ℝ=> x*shunt x) atTop (𝓝 0):=by
   have hp:= hx.mul hx; rw [mul_zero] at hp; exact hp.congr' (b₀.mono fun _ p=>p.symm)
 have hp:Tendsto (fun x:ℝ=> (x*shunt x)*spikes a x) atTop (𝓝 0):=by
    refine squeeze_zero' ?_ ?_ (g:=fun x:ℝ=> x⁻¹*x⁻¹*(4*x/a+3)) ?_; rotate_left
    · filter_upwards [b₀,eventually_ge_atTop (1:ℝ)] with x v e; rw [v]; apply mul_le_mul_of_nonneg_left _ (mul_self_nonneg ..); -- inspect goals
      apply le_trans (spike_bounds h e).2.2; gcongr; exact Real.log_le_self (zero_le_one.trans e)
    · have ht:= (hx.mul_const (4/a)).add ((hx.mul hx).mul_const 3); rw [zero_mul,zero_mul,zero_mul, add_zero] at ht; apply ht.congr'; filter_upwards [eventually_gt_atTop (0:ℝ)] with x h; field_simp
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x v; have h:=shunt_p x; positivity
 have hu:Tendsto (fun x:ℝ=> x*Real.exp (-(a*spikes a x))) atTop (𝓝 0):=by
   apply squeeze_zero' _ _ he
   · filter_upwards [eventually_gt_atTop (0:ℝ)] with x v; positivity
   filter_upwards [eventually_ge_atTop (1:ℝ)] with x v; apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans v); exact Real.exp_le_exp.mpr (by have hx:= (div_le_iff₀ h).1 (spike_bounds h v).2.1; linarith [Real.log_nonneg v])
 have hs:= (he.const_mul (16*K)).add ((hp.add hu).const_mul (8*c^2)); simp only [mul_zero,add_zero] at hs; apply hs.congr; intro x; unfold Crust.bend_cost; ring
variable {L N:Side}
def Xentry (a c d k:ℝ)(x:ℝ) := x*(3^4*(Fintype.card PlaqAxes:ℝ)*Crust.bend_cost (spikes a x) (2*shunt x) a c k) + (3^4+3^4)*(x*(c*temp x^3+c*temp x^4)+d*temp x^2)
lemma Xentry₀ (h:0<a) : Tendsto (Xentry a b c d) atTop (𝓝 0):= by
 have he:= ((ripple (c:=b) h d).const_mul (3^4*(Fintype.card PlaqAxes:ℝ))).add ((uproot b c).const_mul (3^4+3^4))
 simp only [mul_zero,add_zero] at he; apply he.congr; intro x; unfold Xentry; ring
lemma towers : Fintype.card (Crust.Grid.Tower 3)=81:=by unfold Crust.Grid.Tower Region.Rail Region.Uniform; erw [Fintype.card_pi_const]; norm_num
lemma Xledger (u:N.val=L.val*3)(a b c d x:ℝ) : Xentry a b c d x * L.val^4=Crust.Grid.Plan.cellsCost N 3 L x (temp x) b c (spikes a x) (2*shunt x) a d:=by
 unfold Plan.cellsCost Xentry; rw [towers,show Fintype.card (Face (Per N))= N.val^4 * Fintype.card PlaqAxes from (Fintype.card_prod ..).trans (by rw [site_card])]; unfold taxY; rw [u]; push_cast; ring
-- density exponent credit. control against log q power
abbrev dutyM (q:ℝ) := q^4
lemma district (t:0<a)(w:0 ≤ b)(K:ℝ)(h:0<K)(L:ℝ)(p:0≤L) : ∀ᶠ x:ℝ in atTop, ∀ q:ℝ,dutyM (Real.log x) ≤ q → L+(spikes a x:ℝ)* q^3 * b * |Real.log (shunt x/4)| ≤ K * q^4 := by
 let l:=Real.log (4:ℝ); let D:= 4/a+3; let k:= Real.log; have hc:0≤ l:=Real.log_nonneg (by norm_num); have hD:0<D:=by unfold D; positivity
 filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1, (show Tendsto (fun x:ℝ=>K*Real.log x) atTop atTop from Real.tendsto_log_atTop.const_mul_atTop h).eventually_ge_atTop (L+D*b*(3+l)),eventually_ge_atTop (1:ℝ)] with x v g e
 intro q u; change (k x)^4 ≤ q at u; let y:= k x; change y^4 ≤ q at u; change 1 ≤ y at v
 have hv:y^3 ≤ q:=(pow_le_pow_right₀ v (by decide : (3:ℕ)≤4)).trans u
 have hz:1≤q:=(one_le_pow₀ v).trans u; have hf: spikes a x ≤ D*y:=(spike_bounds t e).2.2.trans (by unfold D; dsimp only [y,k] at *; rw [mul_div_right_comm]; linarith)
 have he:|Real.log (shunt x/4)|≤(3+l)*y:=by rw [Real.log_div (shunt_p x).ne' (by norm_num),shunt,Real.log_exp]; change |-3*y-l| ≤ _; rw [abs_of_nonpos (by linarith)]; nlinarith
 have hs:D*y*q^3*b*((3+l)*y)=(D*b*(3+l))*y^2 * q^3:=by ring
 apply (add_le_add_right (show (spikes a x:ℝ)* q^3 * b * |Real.log (shunt x/4)|≤ (D*b*(3+l))*y^2*q^3 from (le_trans ?_ hs.le)) L).trans; swap
 · gcongr
 let G:=D*b*(3+l); have hL: L ≤ L*y^2*q^3:=le_trans (le_mul_of_one_le_right p (one_le_pow₀ v)) (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hz))
 change L+G*y^2*q^3 ≤ _; change L+G≤K*y at g; calc
 _ ≤ (L+G)*y^2*q^3 := by linarith only [hL]
 _ ≤ (K*y)*y^2*q^3:= by gcongr
 _ ≤ _:= by nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hv (by positivity : 0≤q^3)) h.le]
#print axioms district
end YM.CF.Buffered.Alloy.Tariff

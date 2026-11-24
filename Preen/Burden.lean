import Mathlib
set_option autoImplicit false
noncomputable section
namespace YM.Preen
open Real Function Filter
open scoped Topology
-- X_s=X+o j; j=hike(d); n= k*(d+1)^2; X_s comps i*.Prove universal for any sequences xj etc inputs y
section beat
abbrev peaks(d:ℕ):ℕ:=2^(2^d:ℕ)
abbrev breeze(x:ℝ):ℝ:= Real.exp (Real.log (Real.log x)^2) -- precedence verify equals exp(loglog x ^2)
abbrev shoreH(d:ℕ):ℝ:= Real.exp ((d:ℝ)^2)
lemma goes_town:Tendsto peaks atTop atTop:= (tendsto_pow_atTop_atTop_of_one_lt (show 1<(2:ℕ) by decide)).comp (tendsto_pow_atTop_atTop_of_one_lt (show 1<(2:ℕ) by decide))
lemma shore_up: Tendsto shoreH atTop atTop:= Real.tendsto_exp_atTop.comp ((tendsto_pow_atTop (by decide:(2:ℕ)≠0)).comp tendsto_natCast_atTop_atTop) -- check
lemma shore_paid(d:ℕ):1 ≤ shoreH d:=by simpa using Real.exp_le_exp_of_le (sq_nonneg (d:ℝ))
lemma twoAlarms: (1:ℝ)/2 < log 2 ∧ log 2 ≤ 1:=by constructor <;> linarith only [Real.log_two_gt_d9,Real.log_two_lt_d9] -- splits?
private lemma plain_fee : Tendsto (fun d : ℕ=> (((d:ℝ)^2+1)* (2:ℝ)⁻¹^d)) atTop (𝓝 0):=by
 have h:Summable (fun d:ℕ=> (d:ℝ)^2*(2:ℝ)⁻¹^d):= summable_pow_mul_geometric_of_norm_lt_one _ (by norm_num)
 have B:= h.tendsto_atTop_zero.add (tendsto_pow_atTop_nhds_zero_of_lt_one (r:=(2:ℝ)⁻¹) (by positivity) (by norm_num))
 rw [add_zero] at B; exact B.congr (fun d=>by ring)
lemma arc_paints (k:ℕ):∀ᶠ d:ℕ in atTop, k*d^2 ≤ peaks d:=by
 have he:= (plain_fee.const_mul (k:ℝ)); rw [mul_zero] at he
 filter_upwards [he.eventually (gt_mem_nhds zero_lt_one)] with d u
 have hx:(k:ℝ)*(d:ℝ)^2 ≤ 2^d:= by
    rw [inv_pow] at u; have hp:0<(2:ℝ)^d:=by positivity
    field_simp at u; nlinarith only [u,Nat.cast_nonneg (α:=ℝ) k]
 have hp:k*d^2 ≤2^d:=by exact_mod_cast hx
 exact hp.trans (le_of_lt (Nat.lt_two_pow_self (n:=2^d)))
lemma x_here (b w:ℝ)(h:0<b)(k:ℕ) (X:ℕ→ℝ)(a:∀s:ℕ,X s=w+(s:ℝ)*b) :∀ᶠ d:ℕ in atTop, peaks d*(b/2:ℝ) ≤ X (peaks d) ∧ X (peaks d+k*d^2) ≤ (peaks d:ℝ)*(3*b):=by
 have hy:Tendsto (fun i:ℕ=> (peaks i:ℝ)*(b/2)) atTop atTop:= ((tendsto_natCast_atTop_atTop.comp goes_town).atTop_mul_const (half_pos h)) -- helper
 filter_upwards [hy.eventually_gt_atTop (|w|),arc_paints k] with d y e
 rw [a,a,Nat.cast_add]; have h': (↑(k*d^2):ℝ)*b ≤ (peaks d:ℝ)*b:= mul_le_mul_of_nonneg_right (by exact_mod_cast e) h.le
 obtain ⟨l,r⟩:=abs_lt.mp y; constructor<;> linarith only [l,r,h',h]
-- log via sandwich α*2^d / log? logX ≍ 2^d. then loglog ≍ d
lemma mint_arctic (b:ℝ)(h:0<b) (X:ℕ→ℝ)(e:∀ᶠ d:ℕ in atTop,(peaks d:ℝ)*(b/2)≤X d ∧ X d ≤ (peaks d:ℝ)*(3*b)): ∀ᶠ d:ℕ in atTop, 0<X d ∧ shoreH d ≤ breeze (X d)^25 ∧ breeze (X d)≤ shoreH d^4 ∧ Real.log (X d) ≤ (2:ℝ)*2^d :=by
 have ht:Tendsto (fun d:ℕ=> (2:ℝ)^d) atTop atTop:= tendsto_pow_atTop_atTop_of_one_lt one_lt_two
 have hp:Tendsto (fun d:ℕ=>(d:ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop
 filter_upwards [e,ht.eventually_gt_atTop (|log (3*b)|),ht.eventually_gt_atTop (|8*log (b/2)|),hp.eventually_gt_atTop (10*(|log 2|+1))] with d e t v p
 have hN:(peaks d:ℝ)=(2:ℝ)^(2^(d:ℕ):ℕ):= by push_cast [peaks]; rfl -- lemma maybe no goals
 have hn:0 < (peaks d:ℝ):=by rw [hN]; positivity
 have hX:0<X d :=(mul_pos hn (by linarith)).trans_le e.1
 have hL:(2:ℝ)^d/4 ≤ log (X d)∧ log (X d) ≤ 2*(2:ℝ)^d:=by
    simp only [hN] at e hn -- changes pos
    have lo:= Real.log_le_log (mul_pos hn (half_pos h)) e.1
    have hi:= Real.log_le_log hX e.2
    rw [Real.log_mul (by positivity) (by linarith),Real.log_pow] at lo hi
    push_cast at lo hi
    obtain ⟨l,r⟩:= abs_lt.mp t; obtain ⟨l',r'⟩:=abs_lt.mp v
    obtain ⟨a1,a2⟩:=twoAlarms; have hk:0≤(2:ℝ)^d:=by positivity
    constructor<;> nlinarith only [lo,hi,r,l',a1,a2,hk]
 have hf:0 < Real.log (X d):=(by positivity : (0:ℝ)<2^d/4)|>.trans_le hL.1
 have lo:=Real.log_le_log (by positivity : (0:ℝ)<2^d/4) hL.1
 have hi:=Real.log_le_log hf hL.2
 rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at lo; rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hi
 rw [show Real.log 4=2*log 2 from (by rw [show (4:ℝ)=2*2 by norm_num, Real.log_mul two_ne_zero two_ne_zero]; ring)] at lo
 obtain ⟨a,a'⟩:=twoAlarms; rw [abs_of_pos (by linarith:0<log 2)] at p; have hd:0<(d:ℝ):=by linarith only [a,p]
 have g: (d:ℝ)/5 ≤ Real.log (Real.log (X d)) ∧ Real.log (Real.log (X d)) ≤ 2*d:=by constructor <;> nlinarith only [p,lo,hi,a,a',hd]
 unfold breeze shoreH
 refine ⟨hX,?_,?_,hL.2⟩
 · rw [← Real.exp_nat_mul,Real.exp_le_exp]; norm_num; have hZ:= sq_le_sq₀ (by positivity :0 ≤(d:ℝ)/5) (by linarith only [g.1,hd]: 0≤Real.log (Real.log (X d)))|>.2 g.1; linarith only [hZ]
 rw [← Real.exp_nat_mul,Real.exp_le_exp]; norm_num; have hZ:=(sq_le_sq₀ (by linarith only [g.1,hd]:0≤Real.log (Real.log (X d))) (by positivity : 0≤2*(d:ℝ))).2 g.2; linarith only [hZ]
end beat
#print axioms mint_arctic
end YM.Preen

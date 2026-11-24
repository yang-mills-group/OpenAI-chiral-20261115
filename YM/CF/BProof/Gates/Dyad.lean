import YM.CF.BProof.Angular.Relative
import YM.CF.BProof.PL

/- deterministic dyadic choices. use clock-in-log rather than choose and uniqueness. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Gates
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Finset
open scoped Topology BigOperators Classical
local notation "G"=> SU.group
variable (L:Side)(w:ℕ)(y v x:ℝ)

def ladder (x:ℝ) := ⌈ Real.log x/ Real.log 2 ⌉₊
lemma scales (v:1≤ x): x ≤ ((2^ladder x:ℕ):ℝ) ∧ ((2^ladder x:ℕ):ℝ)<2*x:=by
 let t:= Real.log 2; let u:= Real.log x /t; let k:=ladder x; have ht:0<t:=Real.log_pos one_lt_two; have hx:0<x:=lt_of_lt_of_le zero_lt_one v; have hv : u≤(k:ℝ):= Nat.le_ceil u; have he : (k:ℝ)< u+1:= Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg v) ht.le)
 have ha: ((2^ladder x:ℕ):ℝ)=Real.exp (k*t):=(by push_cast; rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<2)]); rw [ha]; refine ⟨?_,?_⟩
 · nth_rw 1 [← Real.exp_log hx]; exact Real.exp_monotone ((div_le_iff₀ ht).mp hv)
 have h:(k:ℝ)*t<u*t+t:= (mul_lt_mul_of_pos_right he ht).trans_eq (by rw [add_mul,one_mul]); apply (Real.exp_lt_exp.mpr h).trans_eq; unfold u; rw [div_mul_cancel₀ _ ht.ne',Real.exp_add,Real.exp_log hx,Real.exp_log (by norm_num : (0:ℝ)<2),mul_comm]
lemma climbs {p:ℝ→ℝ}(h:Tendsto p atTop atTop): Tendsto (fun y=> ladder (p y)) atTop atTop:= by
 apply Tendsto.comp (tendsto_nat_ceil_atTop (α:=ℝ)); exact (Real.tendsto_log_atTop.comp h).atTop_div_const (Real.log_pos one_lt_two) -- tune

-- dyadic and heights for bands construction. Require `y` admitted high (`t(y)` sufficiently small), even periods lower.
def r_P := ladder (sizeP y/(2*L.val))
def LP := 2^(r_P L y)*(2*L.val)
def DP := LP L y - 2*w
def gap := 2*L.val + 2*w
def r_F := ladder (v*Face.rY y)
def gF := 2^(r_F y v)
lemma GP (L:Side)(w:ℕ) : 0<gap L w:=by unfold gap; positivity
lemma PP (L:Side)(y:ℝ) : 0<LP L y:=by unfold LP; have := L.property; positivity
lemma posF : 0<gF y v:=by unfold gF; positivity
lemma growing {a b c:ℝ}(h:0<a∨a=0∧0<b∨a=0∧b=0∧0<c) : Tendsto (fun y=>coin y a b c) atTop atTop:=by
 have hz:=coin_purchases (a:=-a) (b:=-b) (c:=-c) (by grind); have hv:Tendsto (fun y=> coin y (-a) (-b) (-c)) atTop (𝓝[>] 0):= tendsto_nhdsWithin_iff.mpr ⟨hz,Eventually.of_forall fun i=>coin_pos ..⟩; apply (tendsto_inv_nhdsGT_zero.comp hv).congr; intro y; simp only [Function.comp_apply,coin_inv,neg_neg]
lemma F_grows (h:0<v): Tendsto (fun y=>r_F y v) atTop atTop:= by apply climbs; apply Tendsto.const_mul_atTop h; exact growing (b:=-1/2) (a:=1/4) (by norm_num)
lemma P_grows : Tendsto (r_P L) atTop atTop:=by apply climbs; apply Tendsto.atTop_div_const; positivity; exact growing (a:=1) (b:=-2) (by norm_num) -- tune
-- compared log √.
lemma log_log : PL (fun x=>Real.log (Real.log x)):=by
 refine PL.by_le PL.log_y ?_; filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with y hy; have he:0<Real.log y:=one_pos.trans_le hy; rw [abs_of_nonneg (Real.log_nonneg hy),abs_of_nonneg he.le]; linarith [Real.log_le_sub_one_of_pos he]
lemma log_pl (a b c:ℝ): PL (fun y=> Real.log (coin y a b c)):=by
 unfold coin; simp_rw [Real.log_exp]; exact ((PL.log_y.mul (PL.const _)).add ((log_log.pow _).mul (PL.const _))).add (log_log.mul (PL.const _)) -- tune
lemma F_pl (h:0<v): PL (fun y=>(r_F y v:ℝ)):=by
 let z(y):= v*Face.rY y; apply PL.ceil (f:=fun y=>Real.log (z y)/Real.log 2)
 · simp_rw [z,Real.log_mul h.ne' (coin_pos ..).ne',div_eq_mul_inv]; exact ((PL.const _).add (log_pl ..)).mul (PL.const _)
 filter_upwards [((growing (a:=1/4) (b:=-1/2) (c:=0) (by norm_num)).const_mul_atTop h).eventually_ge_atTop 1] with y hy; exact div_nonneg (Real.log_nonneg hy) (Real.log_nonneg one_le_two) -- tune

lemma lengths : Tendsto (DP L w) atTop atTop := by
 rw [tendsto_atTop]; intro k; let X:=fun y=>sizeP y/(2*L.val); have hz: (0:ℝ)<2*L.val:=by positivity
 have hp:Tendsto X atTop atTop:= (growing (a:=1) (b:=-2) (by norm_num)).atTop_div_const hz
 filter_upwards [hp.eventually_ge_atTop 1,(growing (a:=1) (b:=-2) (c:=0) (by norm_num)).eventually_ge_atTop (↑(k+2*w):ℝ)] with y h hy; have hi: ↑(k+2*w) ≤ (LP L y:ℝ):=by refine le_trans hy ?_; unfold LP; push_cast; apply (div_le_iff₀ hz).1; simpa only [X,r_P,sizeP,Nat.cast_pow,Nat.cast_ofNat] using (scales (X y) h).1 -- tune
 unfold DP; have h:= Nat.cast_le.mp hi; omega
lemma scale_domain : ∀ᶠ y:ℝ in atTop, (0< DP L w y ∧ DP L w y+2*w=LP L y) ∧ 0<r_P L y∧ SizedP (LP L y) y∧ sizeP y≤2*(DP L w y:ℝ):=by
 let X:=fun y=>sizeP y/(2*L.val); have hz: (0:ℝ)<2*L.val:=by positivity
 have hp:Tendsto X atTop atTop:= (growing (a:=1) (b:=-2) (by norm_num)).atTop_div_const hz
 filter_upwards [hp.eventually_ge_atTop 1,(P_grows L).eventually_gt_atTop 0,(lengths L w).eventually_gt_atTop (2*w)] with y h hx hv
 obtain ⟨u,b⟩:= scales (X y) h; have he:SizedP (LP L y) y:=by
    unfold LP; constructor
    · exact le_trans ((div_le_iff₀ hz).1 u) (le_of_eq (by unfold r_P X at *; push_cast; rfl)) -- tune
    apply lt_of_le_of_lt _ ( (mul_lt_mul_of_pos_right b hz).trans_eq (by unfold X; field_simp)); exact le_of_eq (by unfold r_P X at *; push_cast; rfl)
 have hl : DP L w y + 2*w =LP L y:=by unfold DP at *; omega
 refine ⟨⟨by omega,hl⟩,hx,he,he.lower.trans ?_⟩; exact_mod_cast (show LP L y≤2*DP L w y by omega)
-- buy `∀ φ PL, PL sizes << DP` uniformly on side.
lemma pl_D (M:ℝ→ℕ)(v:PL fun y=>(M y:ℝ)): ∀ᶠ y in atTop,M y < DP L w y:=by
 filter_upwards [scale_domain L w, coin_strongLt (a:=1/2) (b:=0) (by norm_num) v, coin_budget (a:=1/2) (b:=0) (c:=0) (d:=1) (e:=-2) (f:=0) (by norm_num) 2 1 one_pos] with y hy H hp; have hh:=hy.2.2.2; change _<1*sizeP y at hp; exact Nat.cast_lt.mp (show (M y:ℝ)< DP L w y from by linarith [(le_abs_self _).trans_lt H])
lemma permit (h:0<v)(b:ℕ): ∀ᶠ y in atTop, b≤r_F y v ∧ (gF y v)≤ (DP L w y/32) ∧ v*Face.rY y≤gF y v ∧ (gF y v:ℝ)<2*v*Face.rY y:=by
 have hr:Tendsto Face.rY atTop atTop:= growing (a:=1/4) (b:=-1/2) (by norm_num)
 filter_upwards [(hr.const_mul_atTop h).eventually_ge_atTop 1,(F_grows v h).eventually_ge_atTop b, scale_domain L w, coin_budget (a:=1/4) (b:=-1/2) (c:=0) (d:=1) (e:=-2) (f:=0) (by norm_num) (128*v) 1 one_pos] with y hy H1 H2 H3; let t:=gF y v
 obtain ⟨he,hg⟩:=scales (v*Face.rY y) hy; change (t:ℝ)<_ at hg; refine ⟨H1,?_,he, hg.trans_eq (mul_assoc ..).symm⟩
 have hp:=H2.2.2.2; apply (Nat.le_div_iff_mul_le (by decide)).mpr; change t*32 ≤_; exact_mod_cast (show (t:ℝ)*32≤ DP L w y by change _*Face.rY y < 1*sizeP y at H3; linarith)
end YM.CF.BProof.Gates

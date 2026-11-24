import YM.SU5.Selected.Hill.Valse
import YM.CF.BPress.Scale
import YM.CF.Newt.Stage
/-! late coupling guards for massif r. -/
set_option autoImplicit false
noncomputable section
namespace YM.Hill.Post
open Function Filter Metric Finset Lattice Tree Wilson RG Pressure MeasureTheory Chene Chene.Tail Next.Rank CF CF.BPress Hill.Box Spindle
open scoped Topology BigOperators Classical
variable {G:Gauge}{θ τ σ:ℝ}
def melt (x:ℝ):ℕ:=1+radiusB x
def side(x:ℝ):Side:=⟨(melt x)^3, by unfold melt; positivity⟩
abbrev screen (x:ℝ):= 4*lscale x^3*temp x
@[simp] lemma molten (x:ℝ):(melt x:ℝ)=lscale x:=by unfold melt lscale; push_cast; rfl
lemma silver(x:ℝ): (0:ℝ)<lscale x:=zero_lt_one.trans_le (lscale_one _)
@[simp] lemma stance_ (x:ℝ):((side x).val:ℝ)=(lscale x)^3:= by change (((melt x)^3:ℕ):ℝ)=_; push_cast; rw [molten]
lemma emploi{t:ℝ} (p:0<t)(C:ℝ)(h:0≤C)(k:ℕ):∀ᶠ x in atTop, Real.exp (-(t*melt x))*C ≤ temp x^k:=by
 filter_upwards [CF.Newt.smallF p C (n:=k)] with x v; apply le_trans _ v; apply mul_le_mul_of_nonneg_right _ h; apply Real.exp_monotone; rw [_root_.neg_mul]; apply neg_le_neg; exact mul_le_mul_of_nonneg_left (by exact_mod_cast (Nat.div_le_self (radiusB x) 100000).trans (Nat.le_add_left ..) : (Stores.till x:ℝ)≤ (melt x:ℝ)) p.le -- tune
lemma vilify (C:Clip) :∀ᶠ x in atTop,2 ≤ temp x*Real.exp ((melt x:ℝ)/C.relaxation):=by
 filter_upwards [emploi (show 0< C.relaxation⁻¹ from inv_pos.mpr C.radius_pos) 2 (by norm_num) 1] with x h
 rw [mul_comm (Real.exp _), Real.exp_neg, pow_one] at h -- order adjust div_eq first won't match
 apply (div_le_iff₀ (Real.exp_pos _)).mp; simpa [div_eq_mul_inv,mul_comm C.relaxation⁻¹] using h
open Precision
lemma embers(C:Clip)(L: Rules G)(K:ChartRatio G)(s:0<σ)(p:LocalRatio K)(X:ℝ)(u:0<τ)(v:0<θ):∀ᶠ x in atTop, screen x ≤ L.c ∧ 2*screen x<K.radius ∧ (∀ y:G.Color, ‖y‖≤2*screen x→ K.J y ≤ Real.exp τ) ∧ (rate_ell σ X (melt x)/C.direct ≤ θ^2):=by
 let E:= screen; have hp:NPL E:= PL.times ((PL.const _).mul (PL.scale.pow (k:=3))) npl_temp; have h0:Tendsto (fun x=>2*E x) atTop (𝓝 0):= (hp.const_mul 2).drop
 have hs:Tendsto (fun x=> rate_ell σ X (melt x)/C.direct) atTop (𝓝 0):=by
    simp_rw [rate_ell,tax,molten]; have he:= Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (lscale_late.const_mul_atTop s)); convert! (((he.const_mul X).pow 2).const_mul (Fintype.card PlaqAxes:ℝ)).div_const C.direct using 1; simp
 have hk: ∀ᶠ i in 𝓝 (0:G.Color), K.J i ≤ Real.exp τ:= ( (p.germ _ (Metric.mem_ball_self p.patch)).continuousAt).eventually (ge_mem_nhds (by rw [p.anchored]; exact Real.one_lt_exp_iff.mpr u))
 obtain ⟨ε,q,hK⟩:= Metric.nhds_basis_closedBall.eventually_iff.1 hk; filter_upwards [hp.drop.eventually (ge_mem_nhds L.radius), h0.eventually (gt_mem_nhds p.patch), h0.eventually (ge_mem_nhds q), hs.eventually (ge_mem_nhds (pow_pos v 2))] with x a g b d; exact ⟨a,g,fun y h=> hK (mem_closedBall_zero_iff.mpr (h.trans b)),d⟩
lemma xt_squared{x:ℝ}(p:0<x) : x*temp x^2= drift x^2:=by rw [BPress.temp_eq,mul_pow,gscale p.le,←mul_assoc,mul_inv_cancel₀ p.ne',one_mul] -- tune
lemma npl_three : NPL (fun x=> x*temp x^3):=by
 refine (npl_drift_g 3 1 zero_lt_one).mono ?_; filter_upwards [eventually_gt_atTop (0:ℝ)] with x p; rw [pow_succ,←mul_assoc,xt_squared p, BPress.temp_eq, Real.rpow_one,show ((drift x)^(3:ℝ))=(drift x)^3 from ?_]; apply Eq.le; congr 1; ring
 norm_num -- norm_num [←Nat.cast_ofNat ..., Real.rpow_natCast]
lemma npl_four : NPL (fun x=> x*temp x^4):= by simp_rw [pow_succ (temp _) 3, ← _root_.mul_assoc]; exact npl_three.mul npl_temp.pl
-- prefer joint budget moment use arbitrary PL coefficient, clamp. bound nonlinear of vault_fee by writing EXACT factors times scaled exponential. `S(x)=exp(-σ*r)/temp² ≤1` eventually. plug.
private def res (σ:ℝ)(x:ℝ) := Real.exp (-(σ*lscale x)) / temp x^2
private lemma carry_r (s:0<σ) : PL (res σ):= (PL.const 1).mono (by
 filter_upwards [emploi s 1 zero_le_one 2, eventually_gt_atTop (0:ℝ)] with x h p; have hp:= BPress.temp_pos p; unfold res; rw [abs_of_nonneg (by positivity),abs_one]; exact (div_le_one (pow_pos hp 2)).2 (by simpa [molten] using h))
private lemma divide_p(F:ℝ→ℝ)(p:PL F)(a:ℝ): PL (fun x=> F x / a):=by simp_rw [div_eq_mul_inv]; exact p.mul (PL.const _)
lemma incline_r(U:Clip)(L:Rules G)(X θ:ℝ)(s:0<σ): NPL fun x=> x*vault_fee U L X θ (screen x) σ (melt x):=by
 let c:=L.C+G.colorScale; let g(x:ℝ):= 4*lscale x^3; let A(x:ℝ):=(c*(4:ℝ)^2)*g x^2; let Z(x:ℝ):=X*(c*(2*lscale x)^2 * g x^2+2*res σ x); let f0(x:ℝ):= U.direct*A x^2/θ+ Z x^2/θ; have hp: PL g:=(PL.const _).mul (PL.scale.pow _); have hA: PL A:=(PL.const _).mul (hp.pow _); have hZ:PL Z:=(PL.const _).mul ((((PL.const _).mul (((PL.const _).mul PL.scale).pow (k:=2))).mul (hp.pow _)).add ((PL.const _).mul (carry_r s))); have he:PL f0:= (divide_p _ ((PL.const _).mul (hA.pow _)) _).add (divide_p _ (hZ.pow _) _)
 apply (npl_four.mul he).mono; filter_upwards [eventually_gt_atTop (0:ℝ)] with x p; have hx:= BPress.temp_pos p; have hh:res σ x *temp x^2= Real.exp (-(σ*lscale x)):= div_mul_cancel₀ _ (pow_pos hx 2).ne'; unfold vault_fee summit allowance; push_cast; -- does push also unfolds molten? test
 simp only [molten]; rw [←hh]; apply Eq.le; congr 1; unfold f0 A Z g c screen; ring -- dependent def order
end YM.Hill.Post
#print axioms YM.Hill.Post.incline_r

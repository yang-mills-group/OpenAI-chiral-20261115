import YM.Pressure.Seeds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Size-late gates for the FiniteGaugeData pressure comparisons

exceptional-set suppression ~ exp(-oneFlag x), where oneFlag itself is
larger than any power of log x. Goal for the *small box* part: allow the side
to grow past any *fixed* power of log x. Still not standalone as a volume
limit. State hypotheses as relative bills; these lemmas are independent of
how the sides are chosen and coexist with all the other eventual gates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Pressure Function Real Finset Filter Asymptotics
open scoped Topology

def oneFlag (x : ℝ) := x * temp x^2
def maxTest (x : ℝ) := Real.exp ((Real.log (Real.log x))^2/2) / Real.sqrt (Real.log x)

lemma bigEnough (m : ℕ) : Tendsto (fun x : ℝ=> (Real.log x)^m / maxTest x) atTop (𝓝 0) := by
  let l := Real.log ∘ Real.log
  have hl : Tendsto l atTop atTop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have ht := hl.eventually_ge_atTop ((m+2:ℝ)*2)
  have hb : Tendsto (fun x : ℝ=> ((m:ℝ)+1)*l x-(l x)^2/2) atTop atBot := by
    apply tendsto_atBot_mono' _ _ (tendsto_neg_atTop_atBot.comp hl)
    filter_upwards [ht] with x u
    have hx : l x ≥ (m+2:ℝ)*2 := u
    change _ ≤ -l x; nlinarith [Nat.cast_nonneg (α:=ℝ) m]
  have he : Tendsto (fun x : ℝ=> Real.exp (((m:ℝ)+1)*l x-(l x)^2/2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hb
  refine squeeze_zero' ((Real.tendsto_log_atTop.eventually_gt_atTop 0).mono fun x e => by unfold maxTest; positivity) ?_ he
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with x e
  have hv : 1 ≤ Real.log x := e
  have hp : 0 < Real.log x := zero_lt_one.trans_le hv
  unfold maxTest; rw [div_div_eq_mul_div, Real.exp_sub]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hz : Real.log x = Real.exp (l x) := (Real.exp_log hp).symm
  calc
    _ ≤ (Real.log x)^m * (Real.log x) := by
      gcongr; nlinarith only [Real.sq_sqrt hp.le,hv, Real.sqrt_nonneg (Real.log x)]
    _ = Real.exp ((m+1:ℝ)*l x) := by
      rw [hz, add_mul, Real.exp_add, one_mul, ← Real.exp_nat_mul]

lemma gate_cost : Tendsto (fun x : ℝ=> (maxTest x)^4 * Real.log x / oneFlag x) atTop (𝓝 0) := by
  apply (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).congr'
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0,eventually_gt_atTop (0:ℝ)] with x e p
  change (Real.log x)⁻¹=_; let l := Real.log (Real.log x); let F := Real.exp (l^2/2)
  have hb : Real.exp (l^2) = F^2 := by rw [sq F]; unfold F; rw [ ← Real.exp_add]; ring_nf
  unfold maxTest oneFlag temp; rw [div_pow, mul_pow, hb]
  let L := Real.sqrt (Real.log x); have hq : L^4 = Real.log x ^2 := by nth_rw 1 [show (4:ℕ)=2*2 from rfl]; rw [pow_mul, show L^2=_ from Real.sq_sqrt e.le]
  have he : 0<L := Real.sqrt_pos.2 e; have hg : 0<F := Real.exp_pos _
  rw [inv_pow, Real.sq_sqrt p.le]
  change (Real.log x)⁻¹ = F^4 / L^4*_/(x*(x⁻¹*_)); rw [hq]; field_simp

variable {x N : ℕ→ℝ}

/-- Small-box comparison budget at level zero. -/
structure AdmittedSeries (x N : ℕ→ℝ) : Prop where
  inverse_large : Tendsto x atTop atTop
  side_large : Tendsto N atTop atTop
  infrared_cost : Tendsto (fun i=> N i^4*(Real.log (x i))/oneFlag (x i)) atTop (𝓝 0)

lemma admit_via_ceiling (a : Tendsto x atTop atTop) (b : Tendsto N atTop atTop) {C : ℝ} (_hC : 0 < C)
    (h : ∀ᶠ i in atTop, N i ≤ C * maxTest (x i)) : AdmittedSeries x N := by
  refine ⟨a,b,?_⟩
  have hc := a.eventually (Real.tendsto_log_atTop.eventually_gt_atTop 0)
  refine squeeze_zero' ?_ ?_ (show Tendsto (fun i=> C^4*(maxTest (x i)^4*(Real.log (x i))/oneFlag (x i))) atTop (𝓝 0) from (mul_zero (C^4)) ▸ (gate_cost.comp a|>.const_mul (C^4)))
  · filter_upwards [hc, a.eventually_gt_atTop 0,b.eventually_gt_atTop 0] with i ht hx hn
    unfold oneFlag temp; positivity
  filter_upwards [hc,h,a.eventually_gt_atTop 0,b.eventually_gt_atTop 0] with i hl h hx hn
  have he : 0 < oneFlag (x i) := by unfold oneFlag temp; positivity
  rw [show C^4*((maxTest (x i))^4*_/oneFlag (x i))=(C * maxTest (x i))^4 * (Real.log (x i))/oneFlag (x i) by ring]
  gcongr

lemma flag_value {x : ℝ} (e : 0<x) : oneFlag x = Real.exp (2*(Real.log (Real.log x))^2) := by
  unfold oneFlag temp; rw [mul_pow, inv_pow, Real.sq_sqrt e.le, ←mul_assoc, mul_inv_cancel₀ e.ne',one_mul]; exact (Real.exp_nat_mul _ _).symm

namespace AdmittedSeries
variable (H : AdmittedSeries x N)
local notation "Z" => fun i=>oneFlag (x i)
include H
lemma running : Tendsto (fun i=>oneFlag (x i)) atTop atTop := by
  have ht := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp H.inverse_large)
  apply Tendsto.congr' ((H.inverse_large.eventually_gt_atTop 0).mono fun i p=> (flag_value p).symm)
  exact Real.tendsto_exp_atTop.comp ((ht.atTop_mul_atTop₀ ht|>.const_mul_atTop (show (0:ℝ)<2 by norm_num)).congr (by intro i; rw [sq]; rfl))

lemma extensive_cost : Tendsto (fun i=> N i^4 / oneFlag (x i)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ H.infrared_cost
  · filter_upwards [H.running.eventually_gt_atTop 0] with i e
    have he : 0<oneFlag (x i) := e; positivity
  filter_upwards [H.running.eventually_gt_atTop 0, (Real.tendsto_log_atTop.comp H.inverse_large).eventually_ge_atTop 1] with i e u
  exact div_le_div_of_nonneg_right (le_mul_of_one_le_right (by positivity) u) (show 0<oneFlag (x i) from e).le

lemma exp_bound : ∀ᶠ i in atTop, 1 ≤ N i ∧ N i≤oneFlag (x i) := by
  filter_upwards [H.running.eventually_gt_atTop 0, H.extensive_cost.eventually (ge_mem_nhds one_pos), H.side_large.eventually_ge_atTop 1] with i p t u
  have hu : 1 ≤ N i := u; have hp := (div_le_one (show 0 < oneFlag (x i) from p)).mp t
  exact ⟨u, le_trans ((by simpa using (pow_le_pow_right₀ u (show (1:ℕ)≤4 by omega)) : N i≤N i^4)) hp⟩

lemma sq_log : Tendsto (fun i=> Real.log (Real.log (x i)) ^ 2 / Real.log (x i)) atTop (𝓝 0) := by
  have he := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (show (0:ℝ)<1 by norm_num)).tendsto_div_nhds_zero
  simp only [Real.rpow_one, Real.rpow_two] at he
  exact he.comp (Real.tendsto_log_atTop.comp H.inverse_large)

lemma oneFlag_pow_temp (m : ℕ) : Tendsto (fun i=>oneFlag (x i)^m * temp (x i)) atTop (𝓝 0) := by
  let l(i:ℕ) := Real.log (Real.log (x i)); let y(i:ℕ) := Real.log (x i)
  have hy : Tendsto y atTop atTop := Real.tendsto_log_atTop.comp H.inverse_large
  let c : ℝ := m*2+1; let f(i:ℕ) := c * (l i)^2 - y i/2
  have ht : Tendsto f atTop atBot := by
    have he : Tendsto (fun i=> -(y i/4)) atTop atBot := tendsto_neg_atTop_atBot.comp (hy.atTop_div_const (show (0:ℝ)<4 by norm_num))
    apply tendsto_atBot_mono' _ _ he
    have hp := H.sq_log.const_mul c
    rw [mul_zero] at hp
    filter_upwards [hy.eventually_gt_atTop 0, hp.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/4))] with i u a
    change c*((l i)^2/y i) ≤ 1/4 at a; rw [←mul_div_assoc] at a; have hk := (div_le_iff₀ (show 0<y i from u)).mp a; unfold f; linarith
  refine (Real.tendsto_exp_atBot.comp ht).congr' ?_
  filter_upwards [H.inverse_large.eventually_gt_atTop 0] with i e
  have hb : Real.exp (y i/2)=Real.sqrt (x i) := by rw [← Real.sqrt_sq (Real.exp_pos _).le,← Real.exp_nat_mul, show (2:ℕ)*(y i/2:ℝ)=y i by push_cast; ring]; unfold y; rw [Real.exp_log e]
  change Real.exp (f i)=_
  unfold f temp c; rw [Real.exp_sub,hb, flag_value e,←Real.exp_nat_mul]; unfold l; ring_nf
  rw [Real.exp_add]; ring

lemma tame_bills (m : ℕ) : Tendsto (fun i=> N i^m * temp (x i)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (H.oneFlag_pow_temp m)
  · filter_upwards [H.side_large.eventually_gt_atTop 0] with i h; unfold temp; positivity
  filter_upwards [H.exp_bound] with i u; unfold temp; gcongr; linarith [u.1]; exact u.2

lemma log_budget : Tendsto (fun i=> N i^4*Real.log (N i) / oneFlag (x i)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ H.infrared_cost
  · filter_upwards [H.running.eventually_gt_atTop 0,H.exp_bound] with i e u
    have he : 0<oneFlag (x i) := e; have hU := Real.log_nonneg u.1; positivity
  filter_upwards [H.running.eventually_gt_atTop 0,H.exp_bound,H.inverse_large.eventually_gt_atTop 0,H.sq_log.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/2)), (Real.tendsto_log_atTop.comp H.inverse_large).eventually_gt_atTop 0] with i e u y a b
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) (show 0<oneFlag (x i) from e).le
  apply (Real.log_le_log (zero_lt_one.trans_le u.1) u.2).trans; rw [flag_value y, Real.log_exp]; have h := (div_le_iff₀ (show 0<Real.log (x i) from b)).mp a; linarith
end AdmittedSeries
end YM.CF.Window

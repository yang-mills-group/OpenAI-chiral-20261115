import YM.Pressure.Seeds
import YM.CF.Continuum.Late
import YM.CF.Vale.Dose
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Pressure Function Real Finset Filter Asymptotics
open scoped Topology

lemma sqLog_G : Tendsto (fun i=> Real.log (Real.log (i)) ^ 2 / Real.log (i)) atTop (𝓝 0) := by
  have he := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (show (0:ℝ)<1 by norm_num)).tendsto_div_nhds_zero
  simp only [Real.rpow_one, Real.rpow_two] at he
  exact he.comp (Real.tendsto_log_atTop)

lemma cubeInteger_G (m : ℕ) : Tendsto (fun i=>oneFlag (i)^m * temp (i)) atTop (𝓝 0) := by
  let l(i:ℝ) := Real.log (Real.log (i)); let y(i:ℝ) := Real.log (i)
  have hy : Tendsto y atTop atTop := Real.tendsto_log_atTop
  let c : ℝ := m*2+1; let f(i:ℝ) := c * (l i)^2 - y i/2
  have ht : Tendsto f atTop atBot := by
    have he : Tendsto (fun i=> -(y i/4)) atTop atBot := tendsto_neg_atTop_atBot.comp (hy.atTop_div_const (show (0:ℝ)<4 by norm_num))
    apply tendsto_atBot_mono' _ _ he
    have hp := sqLog_G.const_mul c
    rw [mul_zero] at hp
    filter_upwards [hy.eventually_gt_atTop 0, hp.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/4))] with i u a
    change c*((l i)^2/y i) ≤ 1/4 at a; rw [←mul_div_assoc] at a; have hk := (div_le_iff₀ (show 0<y i from u)).mp a; unfold f; linarith
  refine (Real.tendsto_exp_atBot.comp ht).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with i e
  have hb : Real.exp (y i/2)=Real.sqrt (i) := by rw [← Real.sqrt_sq (Real.exp_pos _).le,← Real.exp_nat_mul, show (2:ℕ)*(y i/2:ℝ)=y i by push_cast; ring]; unfold y; rw [Real.exp_log e]
  change Real.exp (f i)=_
  unfold f temp c; rw [Real.exp_sub,hb, flag_value e,←Real.exp_nat_mul]; unfold l; ring_nf
  rw [Real.exp_add]; ring


private theorem hp_t1: ∀ᶠ i:ℝ in atTop, 2*i*(temp i)^3 ≤ 1 :=by
 have he:= cubeInteger_G 1
 filter_upwards [he.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/2))] with i h; unfold oneFlag at h; linarith [h]
structure BigHeart (x:ℝ):Prop where
 trance: 1 ≤ log x
 live : 2 ≤ x
 sale(y:ℝ): Vale.matchedX x y → y*(temp x)^3 ≤ 1 ∧ (sqrt y)⁻¹ ≤ temp x
lemma moneyK': ∀ᶠ i:ℝ in atTop, BigHeart i :=by
 have hx:= (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1
 filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_ge_atTop (2:ℝ),hx,hp_t1] with i b c d u; refine ⟨b,c,?_⟩; intro y e; have hi:0< i:= zero_lt_two.trans_le c; have ht: 0<y:= (half_pos hi).trans_le e.1 -- replace
 constructor
 · exact (mul_le_mul_of_nonneg_right e.2 (by unfold temp; positivity)).trans u
 have he:0< sqrt i:=sqrt_pos.mpr hi; have hv:0<sqrt y:=sqrt_pos.mpr ht; have hz:1≤ log (log i):=d
 unfold temp; have hE:2≤ Real.exp (log (log i)^2):=by nlinarith [Real.add_one_le_exp (log (log i)^2)]
 refine le_trans ?_ (mul_le_mul_of_nonneg_left hE (by positivity)); rw [show (sqrt i)⁻¹*(2:ℝ)=(sqrt i/2)⁻¹ by field_simp]; exact inv_anti₀ (by positivity) (by nlinarith [Real.sq_sqrt hi.le,Real.sq_sqrt ht.le,e.1])

lemma BigHeart.budget {x:ℝ} (h:BigHeart x)(y:ℝ)(t:Vale.matchedX x y): y*(temp x)^3 ≤ 1 ∧ (sqrt y)⁻¹ ≤ temp x∧ 0<y∧ Real.log ((sqrt y)⁻¹) ≤ Real.log ((sqrt x)⁻¹)+2 ∧ |Real.log ((sqrt y)⁻¹)| ≤ radiusB x + 1 :=by
 have he:= h.live; have ht:1≤y:= le_trans (by linarith) t.1; have hy:=zero_lt_one.trans_le ht; have hX:=h.trance; have hx:(0:ℝ)<x:=by linarith
 refine ⟨(h.sale _ t).1,(h.sale _ t).2,hy,?_⟩; rw [Real.log_inv, Real.log_inv, Real.log_sqrt (by linarith), Real.log_sqrt (by linarith),abs_neg,abs_of_nonneg (div_nonneg (Real.log_nonneg ht) (by norm_num))]
 have hp:= Real.log_le_log (show 0<x/2 by positivity) t.1; have hh:=Real.log_le_log hy t.2; rw [Real.log_div hx.ne' two_ne_zero] at hp; rw [Real.log_mul two_ne_zero hx.ne'] at hh
 have ha: Real.log x^2 ≤ (radiusB x:ℝ):=Nat.le_ceil ..; constructor <;> nlinarith [Real.log_le_sub_one_of_pos zero_lt_two]
end YM.CF.Window

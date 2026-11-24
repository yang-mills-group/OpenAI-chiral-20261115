import YM.SU5.Gleam.Danube
import YM.Next.FLUCTUATIONS.Scales
import YM.Work.E09.Scales
import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE_1AD.LogFunding
/-! # Growth estimates -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
namespace clocks
open Work.E09 AnalyticBridge.Annulus1AD
abbrev height (x:ℝ):ℕ:= radiusB x
local notation "B" x:max=> (height x:ℝ)
local notation "τ" x:max=> temp x
abbrev pace (L:Side)(x:ℝ) := 100*(L.val:ℝ)^2*(height x:ℝ)^6 *temp x
def moder (b w:ℕ)(L:Side):Prop:= b^3 ≤ w ∧ w ≤ L.val*b^3
lemma pace_le (L:Side) : ∀ᶠ x:ℝ in atTop,∀ w:ℕ, moder (height x) w L → suitedFee w (temp x)≤ pace L x :=by
 filter_upwards [eventually_gt_atTop 0, Work.E08.eventual_radiusB 1] with x hx h w g
 let W:=L.val * B x ^3; have he:(w:ℝ)≤W:= by unfold W; exact_mod_cast g.2
 have hl: 1 ≤ B x:= by exact_mod_cast h
 have hm: 1≤ (w:ℝ):= by exact_mod_cast (show 1 ≤ w from (one_le_pow₀ h).trans g.1)
 have ht: 0 ≤ τ x:= (temp_pos hx).le
 unfold suitedFee pace; calc
    _ ≤ 9*W*(4* temp x*(2*W)):= by have hv:0≤W:= zero_le_one.trans (hm.trans he); gcongr <;> linarith
    _ =72* W^2 *temp x:=by ring
    _ ≤100 * _ * _ *_:=by unfold W; ring_nf; gcongr; norm_num
lemma heel (L:Side)(k:ℕ): Tendsto (fun x=> (B x)^k * pace L x) atTop (𝓝 0):=by
 have h:= (radiusB_temp (k+6)).const_mul (100*(L.val:ℝ)^2); rw [mul_zero] at h; apply h.congr; intro x; unfold pace height; rw [pow_add]; ring
lemma cubic (k:ℕ) : Tendsto (fun x=> B x ^ k * (x*temp x^3)) atTop (𝓝 0):=by
 refine squeeze_zero' ?_ ?_ (radiusB_small (1/5) (by norm_num) k).tendsto_div_nhds_zero
 · filter_upwards [eventually_gt_atTop 0] with x hx; have h:=temp_pos hx; positivity
 filter_upwards [eventually_gt_atTop 0,temp_cost (1/10) (by norm_num)] with x hx g
 rw [div_eq_mul_inv]; apply mul_le_mul_of_nonneg_left _ (by positivity); calc
 _ ≤ x * (x^(-(1/2:ℝ)+1/10))^3:= by gcongr; exact (temp_pos hx).le
 _ = _:= by
   rw [←Real.rpow_natCast (x^(-(1/2:ℝ)+1/10)), ←Real.rpow_mul hx.le]; nth_rw 1 [←Real.rpow_one x]; rw [← Real.rpow_add hx]; push_cast; norm_num [show 1+(-(1/2:ℝ)+1/10)*3= -(1/5) by norm_num, Real.rpow_neg hx.le]
lemma pillar (L:Side)(k:ℕ) : Tendsto (fun x=> B x ^ k * (x*pace L x ^3)) atTop (𝓝 0):=by
 let a:ℝ:=100 * L.val ^ 2; have hp:= (cubic (k+18)).const_mul (a^3); rw [mul_zero] at hp; apply hp.congr; intro x; unfold a pace height; rw [pow_add]; ring
lemma margin_fee (J:ChartRatio G)(D:LocalRatio J)(v:ℝ)(h:0 ≤ v): ∃ A>(0:ℝ), ∀ᶠ x:ℝ in atTop,∀ b:ℝ,x/2≤b → b ≤ 2*x → margin J b v ≤ A * B x:=by
 let a:= logCash J; let u:ℝ:= Fintype.card G.ColorIndex; have he:= logCash_nonneg J; have hp:0 ≤ u:= by unfold u; positivity
 refine ⟨2*a+1+u*v,by unfold a; positivity,?_⟩; filter_upwards [eventually_ge_atTop 1,Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx w b g l
 have ht: Real.log x ^ 2 ≤ B x:= Nat.le_ceil _; unfold margin; apply (add_le_add_left (price_spare J D.scale hx ⟨g,l⟩) _).trans; have hf: Real.log x ≤ B x:=by nlinarith only [ht,w]
 change a* _+ u/2*v≤ (2*a+1+u*v)*_; change 0≤ a at he; nlinarith only [hf,mul_le_mul_of_nonneg_left hf he,mul_le_mul_of_nonneg_left w he,(w.trans hf),mul_le_mul_of_nonneg_left (w.trans hf) (mul_nonneg hp h),mul_nonneg hp h,w]
lemma dust_money (k:ℕ)(t:ℝ)(s:0 ≤ t) : ∀ᶠ x:ℝ in atTop, t* B x ^ k ≤ x*temp x^2:=by
 let D(x:ℝ):= Real.exp (Real.log (Real.log x)^2); have ht(x:ℝ)(h:0<x): x * temp x^2= D x ^2:=by unfold temp; rw [mul_pow, inv_pow,Real.sq_sqrt h.le, ← mul_assoc, mul_inv_cancel₀ h.ne',one_mul]
 filter_upwards [eventually_gt_atTop 0,Real.tendsto_log_atTop.eventually_gt_atTop 1, (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (max (1:ℝ) (Real.log (t+1)+ (k:ℝ)*4+3))] with x hx ht' h
 let l:= Real.log x; let b:=Real.log l; have hl:1≤b:= le_trans (le_max_left ..) h; have hb:Real.log (t+1)+(k:ℝ)*4+3 ≤ b:= le_trans (le_max_right ..) h; have hk:0≤ Real.log (t+1):=Real.log_nonneg (by linarith); have he : B x ≤ l^4:=by -- l≥ e^1 ≥2
    have ha:2≤l:=by
       have hL:b+1 ≤ Real.exp b:= Real.add_one_le_exp _; rw [Real.exp_log (zero_lt_one.trans ht')] at hL; linarith only [hL,hl]
    have hp : B x ≤ l^2+1:= (Nat.ceil_lt_add_one (sq_nonneg l)).le; have h:4≤ l^2:= by nlinarith only [ha];
    nlinarith only [ha,hp,h,(sq_nonneg (l^2-3))]
 apply le_trans (mul_le_mul (le_of_lt (lt_add_one t)) (pow_le_pow_left₀ (Nat.cast_nonneg _) he k) (show 0≤ B x ^ k by positivity) (by positivity))
 rw [ht x hx]; apply (Real.log_le_log_iff (by unfold l; positivity) (by unfold D; positivity)).mp
 have hg:0<l:= zero_lt_one.trans ht'
 rw [Real.log_mul (by positivity) (by positivity),Real.log_pow, Real.log_pow,Real.log_pow]; unfold D; rw [Real.log_exp]; norm_num only [Nat.cast_ofNat]; change _+(k:ℝ)*(4*b) ≤2*b^2
 nlinarith only [hl,hb,hk,mul_le_mul_of_nonneg_right hb (zero_le_one.trans hl),mul_le_mul_of_nonneg_left hl hk]
include G in
lemma tail_gone (σ:ℝ)(h:0<σ) : ∀ᶠ x:ℝ in atTop, trail σ (height x) ≤ x⁻¹:=by
 filter_upwards [Next.Fluctuations.tail_delay G 1 _ h] with x hx
 have p : betaF G x 1=x:=by simp [betaF]
 rw [p] at hx; exact le_trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (show (Stores.till x:ℝ)≤ height x by exact_mod_cast Nat.div_le_self (height x) _) (neg_nonpos.mpr h.le))) hx
include G in
lemma parliament (q:Clip) : ∀ᶠ x:ℝ in atTop,∀ p:BudgetPoint, p.threshold=temp x → EnoughMark q p (height x) :=by
 let σ:= q.relaxation⁻¹; have h:0 < σ:= inv_pos.mpr q.radius_pos
 filter_upwards [eventually_gt_atTop (0:ℝ),Real.tendsto_sqrt_atTop.eventually_ge_atTop 2,tail_gone (G:=G) σ h] with x hx hi hl p e
 have hp:0 < Real.sqrt x:= Real.sqrt_pos.mpr hx; have ht : x ≤ Real.exp (σ* B x):= by rw [←inv_le_inv₀ (Real.exp_pos _) hx]; apply hl.trans'; rw [←Real.exp_neg,←neg_mul]; rfl -- hl trail def
 have hv: (Real.sqrt x)⁻¹ ≤ τ x:= le_mul_of_one_le_right (by positivity) (Real.one_le_exp (sq_nonneg _))
 unfold EnoughMark; rw [e]; apply (mul_le_mul hv (le_trans ht ?_) hx.le (temp_pos hx).le).trans'
 · exact hi.trans_eq (by nth_rw 3 [← Real.sq_sqrt hx.le]; field_simp)
 apply Real.exp_monotone; rw [div_eq_mul_inv,mul_comm σ]; apply mul_le_mul_of_nonneg_right _ h.le; exact Nat.cast_le.mpr (Nat.le_add_right ..)
end clocks
end YM.Gleam
#print axioms YM.Gleam.clocks.parliament

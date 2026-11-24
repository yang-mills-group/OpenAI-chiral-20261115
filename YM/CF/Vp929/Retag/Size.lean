/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Vp929.Retag.Mint
import YM.CF.Vp929.Stage.API
import YM.Extra.WILSON_STARTUP.Clock
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.SplitFlag
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade
open scoped Mew
open Jet SU Taxi Rue
open WilsonStartup
/-! Factor the gas sum. -/
open Py Py.Rate
open Real (log sqrt)
variable (c:Clip) (hc:c.direct≤1) (L:Side)
lemma temp_boot (x:ℝ)(hx:0<x) : Pressure.temp x=Timing.temp (log x):=by
  have he:(sqrt x)⁻¹ = Real.exp (-(log x/2)):=by rw [Real.exp_neg,Real.sqrt_eq_rpow,Real.rpow_def_of_pos hx]; congr 2; ring
  rw [Pressure.temp,Timing.temp,Real.exp_add,he]
lemma temp_square (x:ℝ)(hx:0<x) : (Timing.M (log x))^2=x*Pressure.temp x^2:=by rw [Pressure.temp,mul_pow,inv_pow,Real.sq_sqrt hx.le,←mul_assoc,mul_inv_cancel₀ hx.ne',one_mul]; rfl
lemma winter_fit (x s:ℝ)(hs:0<x)(hx:Real.exp 1 ≤ x)(t:x ≤ s)(w:s ≤ 4*x) : Pressure.temp x ≤ 2*Pressure.temp s:=by
  let M(x:ℝ):=Timing.M (log x); have h: M x≤ M s:= by
    have hu : 1 ≤ log x:= (Real.le_log_iff_exp_le hs).mpr hx; have hp:0≤ log (log x):=Real.log_nonneg hu
    apply Real.exp_le_exp.mpr; gcongr
  have ht:=Work.E09.temp_pos hs; have he := Work.E09.temp_pos (hs.trans_le t); have hc:=pow_le_pow_left₀ (le_of_lt (Real.exp_pos ..)) h 2; change (Timing.M (log x))^2≤ (Timing.M (log s))^2 at hc; rw [temp_square x hs,temp_square s (hs.trans_le t)] at hc; have u : Pressure.temp x^2 ≤ (2*Pressure.temp s)^2:= le_of_mul_le_mul_left (by linarith [mul_le_mul_of_nonneg_right w (sq_nonneg (Pressure.temp s))]) hs; nlinarith
lemma leaf_room : ∀ᶠ x:ℝ in atTop, (x^2)⁻¹≤ dleaf L x:=by
  set g:= SU.group.slopeConstant * log L.val
  filter_upwards [eventually_ge_atTop g, eventually_ge_atTop (3:ℝ), (Scales.year SU.group L).eventually_gt_atTop 0] with x hg hx he
  have hp:0<x:=by linarith
  have hs:sqrt (Scales.y SU.group L x) ≤ x:=by rw [Real.sqrt_le_left hp.le]; change x+g≤_; nlinarith
  have ht: x⁻¹ ≤ Pressure.temp x:= by
    unfold Pressure.temp; refine (inv_anti₀ (Real.sqrt_pos.2 hp) ((Real.sqrt_le_left hp.le).mpr (by nlinarith))).trans (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity)))
  have hh: x⁻¹≤ Scales.g SU.group L x:=inv_anti₀ (Real.sqrt_pos.2 he) hs
  unfold dleaf; rw [←inv_pow,pow_two]; exact mul_le_mul hh ht (by positivity) (lt_of_lt_of_le (by positivity) hh).le
local notation "Mx"=>Timing.M
local notation "qx"=>Timing.quota
/-- We use the full Timing superpolynomial density for the mark prices; relax costs at entry to be passed on. -/
lemma tiny (m:ℕ) (a:ℝ) (ha:0<a) : ∀ᶠ s:ℝ in atTop, Real.exp (qx (log s))-1 ≤ a*(s^m)⁻¹:=by
  let u:=Real.log; let A:=|u (2/a)|+(m:ℝ)
  filter_upwards [Real.tendsto_log_atTop.eventually (Timing.hard_growth 2), Real.tendsto_log_atTop.eventually_ge_atTop 1, Real.tendsto_log_atTop.eventually_ge_atTop (2*A),eventually_gt_atTop (0:ℝ)] with s hs ht hu hp
  let k:=u s; have hm : k^2≤ Mx k:= le_trans hs (Real.exp_monotone (by have h:=sq_nonneg (log k); linarith : (log k)^2 /5≤ (log k)^2)); let q:=qx k
  have he : Real.exp q-1≤2*q := by
    have hb:q≥0:=(Real.exp_pos _).le; have hv:=Real.exp_pos ((log k)^2)
    refine (le_abs_self _).trans ((Real.abs_exp_sub_one_le ?_).trans_eq (by rw [abs_of_nonneg hb])); rw [abs_of_nonneg hb]; apply Real.exp_le_one_iff.mpr; unfold Timing.M; linarith only [hv]
  apply he.trans; change 1≤ k at ht; change 2*A≤ k at hu; have hb : 0≤ (m:ℝ) := by positivity
  calc
    2*q = a*Real.exp (log (2/a) + -(Mx k)/2):=by rw [Real.exp_add,Real.exp_log (by positivity)]; change _=a*((2/a)*q); field_simp
    _ ≤ a*Real.exp (-((m:ℝ)*log s)):=by
      gcongr; apply le_trans _ (by change log (2/a) + -(k^2)/2≤ -((m:ℝ)*k); unfold A u at hu; have hw := le_abs_self (Real.log (2/a)); nlinarith [mul_le_mul_of_nonneg_left ht (abs_nonneg (Real.log (2/a)))])
      linarith
    _ = _:=by rw [Real.exp_neg,Real.exp_nat_mul,Real.exp_log hp]
def ReadyRoom (c:Clip) (L:Side) (y:ℝ) (b:BudgetPoint):Prop :=
  Decent c b ∧ 12≤ b.B ∧ b.threshold≤ Start.threshold SU.group b.order b.power ∧
  TagRoom b (σ:=3*Mx (log y)) (γ:=qx (log y)) ∧ Real.exp (qx (log y))-1 ≤ dleaf L y/1000 ∧
    3*Mx (log y) ≤ y/4*(gain b/2) ∧ ∀ p:BudgetPoint,p.order=6 → p.power=2 → p.threshold ≤ 2*b.threshold → liabilities c b p ≤ gain b/2
include hc
lemma liability_pay : ∀ᶠ y:ℝ in atTop, ∀ b p:BudgetPoint, Location.Boot y b → p.order=6 → p.power=2 → p.threshold ≤ 2*b.threshold → liabilities c b p ≤ gain b/2:=by
  let S:= Fintype.card Signed * Fintype.card PlaqAxes; let C:ℝ:= Start.price SU.group 6 2; have hv : 0 ≤ C:=(Start.constants ..).1.le; let v:= (3:ℝ)^4*(S:ℝ)*(C * 32)
  have hh:Tendsto (fun y:ℝ=> v*((radiusB y:ℝ)^4 * Pressure.temp y) *(Pressure.temp y)^2) atTop (𝓝 0):=by
    have hz:Tendsto Pressure.temp atTop (𝓝 0):=by simpa using Work.E09.radiusB_temp 0
    simpa only [zero_pow (by norm_num : 2≠0), mul_zero] using ((Work.E09.radiusB_temp 4).const_mul v).mul (hz.pow 2)
  filter_upwards [hh.eventually (ge_mem_nhds (show (0:ℝ)<1/32 by norm_num))] with y hy b p h hb hp ht
  have hx:1≤ (b.B:ℝ):=by exact_mod_cast b.B_pos
  have hq:=b.threshold_pos
  let T:=b.threshold; change v*((radiusB y:ℝ)^4 * Pressure.temp y) *(Pressure.temp y)^2≤1/32 at hy; rw [←h.threshold,←h.B] at hy
  calc
    liabilities c b p ≤ share*((3*b.B:ℝ)^4*(S:ℝ))*(C*(2*T)^5):=by
      unfold liabilities Start.item; rw [hp,hb]; unfold C T S; push_cast; rw [mul_assoc ((_+_+_:ℝ)^4)]; have k:= (Start.constants SU.group 6 2).1; have u:=p.threshold_pos; have w:=share_pos; have Hb : 0 ≤ Design.bulk c:=sub_nonneg.mpr hc; refine mul_le_mul (by gcongr; linarith) ?_ (by positivity) (by positivity)
      exact (mul_le_of_le_one_left (b:=Start.price SU.group 6 2*p.threshold^5) (by positivity) (sub_le_self _ c.quadratic_pos.le)).trans (by gcongr)
    _ = share*(v*((b.B:ℝ)^4*T)*(T)^2)*T^2:=by unfold v; ring
    _ ≤ share*(1/32)*T^2:=by have := share_pos; gcongr
    _ = _:=by unfold WilsonStartup.gain T; ring
lemma capacity : ∀ᶠ y:ℝ in atTop, ∀ b:BudgetPoint, Location.Boot y b → ReadyRoom c L y b:=by
  let C:= Fintype.card Signed*Fintype.card PlaqAxes; have hp:=share_pos
  filter_upwards [liability_pay c hc,tiny 2 (1/1000) (by norm_num),leaf_room L,Real.tendsto_log_atTop.eventually Timing.many,Real.tendsto_log_atTop.eventually (Timing.cut c), Real.tendsto_log_atTop.eventually (Timing.nballs.eventually_ge_atTop 12), Real.tendsto_log_atTop.eventually (Timing.shrinking.eventually (ge_mem_nhds (Start.constants SU.group 6 2).2.1)), (Timing.growing.comp Real.tendsto_log_atTop).eventually_ge_atTop ((2:ℝ)*9^4), (Timing.growing.comp Real.tendsto_log_atTop).eventually_ge_atTop (512/share), eventually_gt_atTop (0:ℝ)] with y hy h l hm hq hr he hv ht hx b hb
  let s:= log y; have hB:b.B=Timing.balls s :=hb.B; have hP:b.threshold=Timing.temp s:=hb.threshold.trans (temp_boot _ hx); let Q:=Mx s; change _ ≤ Q at hv ht; have hQ:0<Q:=Real.exp_pos _; have hs:= b.supportExponent; have h12 : 12≤ b.B:=hB.symm ▸ hr
  rw [←hB] at hm
  refine ⟨⟨hc,by omega,?_⟩,h12,?_,⟨?_,?_⟩,h.trans ?_,?_,fun p=>hy b p hb⟩
  · rw [hP,hB]; exact hq
  · rw [hP,hb.order,hb.power]; exact he
  · have hw : (wideBox b.B:ℝ) ≤ 4*Q:= by
      apply le_trans (b:=2^4*((2*b.B+2*b.B+1:ℕ):ℝ)^4) _ (by linarith only [hm]); unfold wideBox; push_cast; rw [←mul_pow]; gcongr; linarith
    have hη : (4:ℝ)*Q ≤ Real.exp (3*Q/2):=by
       have u:=Real.add_one_le_exp (3*Q/4); rw [show (3:ℝ)*Q/2=(3*Q/4)+(3*Q/4) by ring, Real.exp_add]; nlinarith
    rw [hb.exponent]; change _≤ Real.exp (-Q/2); rw [show -Q/2=3*Q/2+(-2*Q) by ring,Real.exp_add]; gcongr; exact hw.trans hη; change (1+1:ℝ)*9^4 -3*Q ≤ -2*Q; linarith only [hv]
  · calc
      _ ≤ Q/4 * qx s := by gcongr; swap; exact le_trans (by gcongr <;> omega) hm; exact (Real.exp_pos _).le
      _ ≤ _:=by unfold Timing.quota; have he:=Real.add_one_le_exp (Q/2); change Q/4*Real.exp (-Q/2) ≤ 1; rw [neg_div,Real.exp_neg]; field_simp; linarith
  · linarith only [l]
  have hg:Q^2=y*b.threshold^2:= by rw [hb.threshold]; exact temp_square _ hx
  change 3*Q ≤ _; unfold WilsonStartup.gain; rw [div_le_iff₀ hp] at ht
  calc
    _ ≤ Q^2*(share/128):=by nlinarith
    _ = _:= by rw [hg]; ring
end YM.CF.SplitFlag

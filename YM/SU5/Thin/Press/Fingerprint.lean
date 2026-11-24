import YM.SU5.Thin.Press.Lilt
import YM.SU5.Thin.Press.Lance
import YM.SU5.Fineness.Cordon
import YM.CF.Vp929.Bank.Tail
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
set_option linter.unusedVariables false
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
open Eire Girt
open VolumeRate
variable {d:ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
variable {A C' Pay h ρ f ff ag Cg x β β' : ℝ} {D : Treaty J q A C' Pay h ρ} {c:Estimate}
open Fineness Sleigh Appel.Rate
open scoped ENNReal
lemma porch_trail (K:Teller SU.group)(R:Patch): ∀ᶠ x in atTop,∀ {m n:Side}(S:StepData m n)(M:Monk SU.group S)(U:Tube SU.group S)(H:Bed){η δ:ℝ},Floor H K.top.clip n η δ→Attached H U.up→ Bid.Sworn H n SU.group→ Newt.Cert R K S U x→ |Corne.arcD U x M+(1/2:ℝ)*Real.log (FreeResolvent.treeMatrix SU.group S M.park H.metric).det| ≤ x^(-(1/3:ℝ))* Fintype.card (Site n):=by
 let v:= K.top.width/4; have hp:0<v:= by unfold v; have h:=K.top.width_pos; positivity
 let k:= FreeResolvent.Affine.headGap SU.group R K.bind K.top.clip; have he:0<k:= FreeResolvent.Affine.headGap_pos ..
 let c:ℝ:=2*(Fintype.card SU.group.ColorIndex:ℝ); have hc:0≤c:=by unfold c; positivity
 have hz:= ((Paddled.tempay (by norm_num : (0:ℝ)<1/8)).scale (c/k)).pure (b:=-(1/3:ℝ)) (by norm_num)
 filter_upwards [hz, Newt.smallF (n:=1) hp (ozPay R K.bind K.top.width K.top.paths SU.group)] with x g w; intro m n S M U H η δ u q e t
 rw [pow_one] at w; rw [mul_comm (x^(-(1/3:ℝ)))]; refine (YM.Fineness.porch S M U H u q e t).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
 exact ((mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right w he.le) hc).trans_eq (show c*(temp x/k) =(c/k)*temp x by ring)).trans g -- rfl? `b:= _` optional invalid
lemma freezeX (ka e:ℝ)(u:0<ka)(t:0<e)(J:Gauge)(L:Side): ∀ᶠ x:ℝ in atTop,Real.exp (-ka*(e*Scales.p J L x)^2) ≤ x^(-(1:ℝ)) := by
 have he:= cover_pay J L 1 (a:=1) zero_lt_one; simp only [pow_one,Real.rpow_one] at he
 filter_upwards [he.eventually (ge_mem_nhds t),Real.tendsto_log_atTop.eventually_ge_atTop (1/ka), Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_gt_atTop (0:ℝ)] with x h w w₁ hv
 have hc:= Scales.pos J L x; rw [Real.rpow_neg_one,←Real.exp_neg (Real.log x)|>.trans (show (Real.exp (Real.log x))⁻¹ =x⁻¹ by rw [Real.exp_log hv])]; apply Real.exp_monotone
 have hz:1 ≤ Real.log x*ka:= (div_le_iff₀ u).1 w; have ht:Scales.b x ≤ e*Scales.p J L x:=(div_le_iff₀ hc).1 h
 have hk:Real.log x ≤ e*Scales.p J L x:= ht.trans' ((show Real.log x ≤ (Real.log x)^2 by nlinarith only [w₁]).trans ((Nat.le_ceil ..).trans (le_add_of_nonneg_left zero_le_one)))
 nlinarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans w₁) hk 2) u.le, mul_le_mul_of_nonneg_right hz (zero_le_one.trans w₁)] -- nlinarith normalization square via combination w1^2 default
lemma frosty (A:Pilot) (R:Patch): ∀ᶠ x:ℝ in atTop,∀ u:ℝ,A.hat R x/4≤u→ |Real.log (Appel.point SU.group u)|≤ x^(-(1/3:ℝ)):=by
 obtain ⟨a,C,P⟩:= Appel.Rate.Patron.exists
 let e:=A.large/4; have hp:0<e:=div_pos A.high (by norm_num)
 let F(x:ℝ):=x^(-(1:ℝ)); have he:∀ᶠ x:ℝ in atTop, 2*C*F x ≤ x^(-(1/3:ℝ)):= ((Paddled.park _).scale (2*C)).pure (by norm_num)
 let t(x:ℝ):=F x*C; have hv:Tendsto t atTop (𝓝 0):= (((Paddled.park (-(1:ℝ))).mul (Paddled.lake C))).lim (by norm_num)
 filter_upwards [freezeX a e P.pos hp SU.group R.L,he, hv.eventually (ge_mem_nhds (by norm_num:(0:ℝ)<1/2)),eventually_gt_atTop (0:ℝ)] with x u₀ v w p u h
 have hP:e*Scales.p SU.group R.L x ≤ u:=h.trans' (le_of_eq (by unfold Pilot.hat e; ring)); have hy:0<e*Scales.p SU.group R.L x:=mul_pos hp (Scales.pos ..); have hz: Real.exp (-a*u^2)*C ≤ t x:=mul_le_mul_of_nonneg_right ((Real.exp_monotone (mul_le_mul_of_nonpos_left (pow_le_pow_left₀ hy.le hP 2) (neg_nonpos.mpr P.pos.le))).trans u₀) (zero_le_one.trans P.earns)
 let k:= Appel.point SU.group u; have hk:0<k:= point_p (hy.trans_le hP); have he:k≤1:= measureReal_le_one
 have h0: 1/k ≤ Real.exp (2*t x):= by refine le_of_tendsto ((arc_guard SU.group).div_const k) ?_; filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop u] with y q v; exact P.toll (hy.trans_le hP) q v hz w
 have hu:= Real.log_le_log (by positivity) h0
 rw [Real.log_div one_ne_zero hk.ne',Real.log_one,zero_sub,Real.log_exp] at hu; change |Real.log k| ≤ _; rw [abs_of_nonpos (Real.log_nonpos hk.le he)]; change _≤_ at v; unfold t at hu; linarith only [hu,v]
end YM.CF.Py.Rate

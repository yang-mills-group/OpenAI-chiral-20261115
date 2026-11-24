import YM.SU5.Fineness.Inches
import Refrain.Flurry
import Refrain.Fees

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
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
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
open Eire Girt
open VolumeRate
variable {d:ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
namespace Fineness
open CF.Refrain
open BProof
open YM.SectorNext.Vacuum
open Pannier YM.Fineness Gaussian ProbabilityTheory
open scoped ENNReal
local notation "G5"=>SU.group
local notation "Yx"=>Scales.y G5 R.L
lemma first_lens (J:ChartRatio G5)(H:LocalRatio J)(K:KernelChoices)(c:ℝ)(p:0<c):∀ᶠ x:ℝ in atTop,∀ b:ℝ,Yx x/2≤ b→∀{m n:Side}(S:StepData m n),S.kernel=K→ |Real.log (S.penaltyZ b G5)-Real.log (spare J b)+halfLie G5 *Real.log K.penalty|≤ c*shrift R.L x:=by
 obtain ⟨C,hC,h⟩:=logarithm_fare J H K
 obtain ⟨a,h'⟩:=eventually_atTop.mp h
 have hP:= cleared R.L c (C*2) (sizeK.main R.L) (by norm_num) p
 filter_upwards [hP,(Scales.year G5 R.L).eventually_gt_atTop (max 0 (2*a))] with x hP hp b hb m n S hs
 have hA: a≤b:=by linarith only [hp,hb,(le_max_right (0:ℝ) (2*a))]
 refine (h' b hA S hs).trans (le_trans ?_ hP)
 let v:= Yx x; have hv:0<v:= (le_max_left ..).trans_lt hp
 have he:0<b:=(half_pos hv).trans_le hb
 change C/Real.sqrt b≤ C*2*|(Real.sqrt v)⁻¹|
 have hf:Real.sqrt v≤ 2*Real.sqrt b:=by nlinarith only [Real.sqrt_pos.mpr hv,Real.sqrt_pos.mpr he,Real.sq_sqrt hv.le,Real.sq_sqrt he.le,hb]
 have hx:=Real.sqrt_pos.mpr hv; rw [abs_of_pos (inv_pos.mpr hx)]; field_simp; linarith only [hf]

lemma snowy_log (J:ChartRatio G5)(H:LocalRatio J):∃ C> (0:ℝ),∀ᶠ t:ℝ in atTop,∀ b> (0:ℝ),|Real.log (shotM J t b)-Real.log (spare J b)| ≤ C*Real.exp (-(t^2/4)):=by
 obtain ⟨C,hC,h⟩:=snow_worth
 have he:=arc_guard G5
 refine ⟨2*C,by positivity,?_⟩
 filter_upwards [eventually_gt_atTop (0:ℝ),he.eventually (le_mem_nhds (by norm_num:(1:ℝ)/2<1))] with t ht hP b hb
 unfold shotM; rw [Real.log_mul (spare_pos J H hb).ne' (Appel.point_p ht|>.ne'),add_sub_cancel_left]
 let P:=Appel.point G5 t; have hp:0<P:=Appel.point_p ht
 have hl:1/2≤P:=hP
 have hf:P≤1:= by change (rice G5).real (closedBall 0 t)≤1; exact measureReal_le_one
 have hx:=Real.log_le_sub_one_of_pos hp
 have hz:= Real.log_le_sub_one_of_pos (inv_pos.mpr hp); rw [Real.log_inv] at hz
 have hS:P⁻¹-1≤2*(1-P):=by field_simp; nlinarith only [mul_nonneg (sub_nonneg.mpr hf) (show 0≤P-1/2 by linarith only [hl])]
 have hR:1-P≤C*Real.exp (-(t^2/4)):=h t ht.le
 rw [abs_le]; change -_≤Real.log P ∧ _; constructor <;> linarith only [hx,hz,hR,hS,hf]
-- t lower as a function of x
lemma second_lens (J:ChartRatio G5)(H:LocalRatio J)(u c:ℝ)(hu:0<u)(hc:0<c):∀ᶠ x in atTop,∀ t:ℝ,u*Scales.p G5 R.L x ≤ t → ∀ b> (0:ℝ),|Real.log (shotM J t b)-Real.log (spare J b)| ≤ c*shrift R.L x:=by
 obtain ⟨C,hC,h⟩:=snowy_log J H
 obtain ⟨D,hD⟩:=eventually_atTop.mp h
 filter_upwards [leek R.L u hu, (Real.tendsto_log_atTop.comp (Scales.year G5 R.L)).eventually_ge_atTop 2, ((Scales.peak G5 R.L).const_mul_atTop hu).eventually_ge_atTop D, (Scales.year G5 R.L).eventually (coin_budget (a:=-1/2) (b:=0) (c:=0) (d:=-1/4) (e:=0) (f:=0) (by norm_num) C c hc)] with x hx hL hf hB t ht b hb
 apply (hD t (hf.trans ht) b hb).trans (le_trans ?_ hB.le)
 unfold BProof.coin; simp only [mul_zero,add_zero]; apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hC.le
 change 2≤Real.log (Yx x) at hL
 nlinarith only [hx,hL,ht,mul_nonneg (sub_nonneg.mpr hL) (show 0≤Real.log (Yx x) by linarith only [hL]),mul_le_mul_of_nonneg_right (hx.trans ht) (show 0≤ t+Real.log (Yx x) from by linarith only [hx,hL,ht])]
end Fineness
end YM.CF.Py.Rate

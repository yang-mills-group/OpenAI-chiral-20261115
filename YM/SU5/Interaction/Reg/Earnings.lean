import YM.SU5.Interaction.Reg.Brim
import YM.CF.Vp929.Stage.Sole
import YM.CF.Roots.Cane

/-! Uniform rate strengthening usable through the regulator comparison at (124). Choose costs post geometry. -/
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
variable {A C' Pay h ρ f ff ag Cg x β β' : ℝ} {D : Treaty J q A C' Pay h ρ} {c:Estimate}
variable {w:Location (R:=R) B m n} {p p' : BudgetPoint}

namespace BScale
open Roots Wray Py Ione

-- Q and w_0 of (124)
abbrev lowerQuota (x:ℝ) := Real.exp ((Real.log (Real.log x))^2)
abbrev numerator (L:Side)(x:ℝ):ℝ := allotΨ L x * lowerQuota x

variable (L:Side)
lemma numeratorBounds : ∀ᶠ x:ℝ in atTop, Real.exp (-(radiusB x:ℝ)/2) ≤ numerator L x ∧ dleaf L x ≤ 2*numerator L x:=by
 let Y(x):=Scales.y SU.group L x
 let t:= SU.group.slopeConstant * Real.log L.val
 filter_upwards [eventually_ge_atTop (2:ℝ),(Scales.year SU.group L).eventually_gt_atTop 0,eventually_ge_atTop t,Real.tendsto_log_atTop.eventually_ge_atTop 4] with x hx v hS b
 let B:=radiusB x; change Real.exp (-(B:ℝ)/2) ≤ _ ∧ _; let y:=Y x; let g:=Scales.g SU.group L x; let w:=lowerQuota x
 have he:y>0:=v; let sol:= Real.sqrt x; have hp:x>0:=by linarith only [hx]
 have hu:1≤ w:= Real.one_le_exp (sq_nonneg _); have hv := (Scales.gauge SU.group L v); change 0<g at hv; have hr: y*g^2=1:= Scales.yg2 SU.group L v
 have hh: y≤2*x:=by change x+t ≤_; linarith only [hS]
 have hk: g^2=1/y:=by rw [eq_div_iff he.ne',mul_comm,hr]
 constructor
 · have hB: (Real.log x)^2 ≤ (B:ℝ):= Nat.le_ceil _; have hy: - (B:ℝ)/2 ≤ -Real.log x + -Real.log x:=by nlinarith only [b,hB]
   refine (Real.exp_monotone hy).trans ?_; rw [Real.exp_add,Real.exp_neg,Real.exp_log hp]; change _≤g^2*w; rw [hk]; apply le_trans _ (le_mul_of_one_le_right (a:=1/y) (by positivity) hu); field_simp; nlinarith only [hh,hx]
 change g*(sol⁻¹*w)≤2*(g^2*w); have hs: sol>0:=Real.sqrt_pos.mpr hp
 have h0: sol⁻¹ ≤ 2*g:=by
    have h1:sol⁻¹ ^ 2≤ 4*g^2:=by rw [inv_pow, show sol^2=x from Real.sq_sqrt hp.le,hk]; field_simp; linarith only [hh,hp]
    nlinarith only [h1,hv,inv_pos.mpr hs]
 rw [←mul_assoc g]; refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h0 hv.le) (zero_le_one.trans hu)).trans_eq (by ring)

open Next.Rank.Thirst
abbrev incidenceConstant :ℝ:= wilt 1*(2*Real.exp 20+1)
def fittedCharge(P:BudgetPoint)(L:Side)(x:ℝ) := (incidenceConstant * (P.B:ℝ)^8)* numerator L x
lemma normalizedRate : ∀ᶠ x:ℝ in atTop,∀(m:Side)(p:BudgetPoint),p.B=radiusB x→(∀(H:ℝ)(E:RegBudget m),0 ≤ H → IncX (fun _=>False) (head_L E) p H (dleaf L x) → IncX (fun _=>False) (head_L E) (ups p) H 1 → LocalHead p (p.supportExponent+10/(p.B:ℝ)) E H (fittedCharge p L x)) := by
 filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop 40,numeratorBounds L] with x h z m p y H E pH u v
 have hp:20+20 ≤ (p.B:ℝ) := by rw [y]; norm_num; exact_mod_cast h -- tune
 let s:=20/(p.B:ℝ)
 let b:= incidenceAt p E pH (bandwidth p 20 (by norm_num) (by linarith only [hp]) u v pH)
 refine LocalHead.raise p b ?_; apply le_trans (mul_le_mul_of_nonneg_left (show _ ≤ (2*Real.exp 20+1)* numerator L x from ?_) (wilty (p.B^2))) (le_of_eq ?_)
 · rw [mul_one,y]; nlinarith only [mul_le_mul_of_nonneg_left z.2 (Real.exp_pos (20:ℝ)).le, z.1]
 unfold fittedCharge incidenceConstant wilt; push_cast; ring
end BScale
end YM.CF.Py.Rate

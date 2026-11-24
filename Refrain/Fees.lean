import YM.SU5.Fineness.Inches
import Refrain.Bottle
import Refrain.Shrift

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
open Pannier YM.Fineness
open YM.SectorNext.Vacuum (narrow linkZ narrow_pos mouth first_asymptotic toll_sharp)
variable {G:Gauge}(J':ChartRatio G)(p:LocalRatio J')
local notation "d'"=> halfLie G
include p
lemma logarithm_fare(g:KernelChoices) :∃ C> (0:ℝ),∀ᶠ b:ℝ in atTop,∀ {m n:Side}(S:StepData m n), S.kernel=g →
 |Real.log (S.penaltyZ b G)-Real.log (spare J' b)+halfLie G *Real.log g.penalty|≤ C/Real.sqrt b:=by
 let t:=g.penalty; have u:=g.penalty_pos
 let v:=narrow J' t; have ht:=narrow_pos J' p _ u
 have he:Real.log v=logFlat J' - d'*Real.log g.penalty:=by
    have hp : (Real.pi / (t/2))>0:= div_pos Real.pi_pos (half_pos u)
    rw [show v=J'.scale * (Real.pi / (t/2)) ^ d' from rfl, Real.log_mul p.scale.ne' (Real.rpow_pos_of_pos hp _).ne',Real.log_rpow hp]
    rw [show Real.pi/(t/2)= (2*Real.pi)/g.penalty from by unfold t; ring,Real.log_div (mul_pos (by norm_num) Real.pi_pos).ne' u.ne', shadowLie]; unfold logFlat; ring
 let f (x:ℝ):= x^(Module.finrank ℝ G.Color)*linkZ G (g.penalty*x^2)
 obtain ⟨C,hc,h⟩:= toll_sharp J' p u
 have hpv:v/2<v:=by change narrow J' t/2<narrow J' t; exact half_lt_self ht
 have hp(x:ℝ)(h1:v/2≤x): |Real.log x-Real.log v|≤ |x-v| *(2/v):=by
    have ha: 0<v:=ht
    have hx:0<x:=by linarith only [ha,h1]
    have hh (y z:ℝ)(yP:0<y)(h:v/2 ≤ z) : Real.log y-Real.log z≤|y-z| *(2/v):=by
       have hz:0<z:=by linarith only [ha,h]
       rw [←Real.log_div yP.ne' hz.ne']; refine (Real.log_le_sub_one_of_pos (div_pos yP hz)).trans (sub_le_iff_le_add.mpr ((div_le_iff₀ hz).mpr ?_))
       field_simp; nlinarith only [mul_le_mul_of_nonneg_left h (abs_nonneg (y-z)),mul_le_mul_of_nonneg_right (le_abs_self (y-z)) ha.le]
    rw [abs_le]; refine ⟨?_,hh _ _ hx hpv.le⟩; have hi:=hh _ _ ha h1; rw [abs_sub_comm] at hi; linarith only [hi]
 have hg:0<v:=ht
 refine ⟨C*(2/v),by positivity,?_⟩
 filter_upwards [eventually_gt_atTop (0:ℝ), Real.tendsto_sqrt_atTop.eventually h,Real.tendsto_sqrt_atTop.eventually ((first_asymptotic J' p _ u).eventually (le_mem_nhds hpv))] with b h k k'
 intro m n S hS
 let a:=Real.sqrt b
 have h0: 0<a:= Real.sqrt_pos.mpr h
 have heq : S.penaltyZ b G = linkZ G (g.penalty*b) := by
   unfold StepData.penaltyZ StepData.penaltyWeight linkZ SectorNext.Vacuum.mouth
   rw [hS]; congr 1; ext x; ring_nf
 rw [← Real.sq_sqrt h.le] at heq
 have k: |Real.log (a^ (Module.finrank ℝ G.Color)*linkZ G (g.penalty*a^2))-Real.log v|≤ C/a*(2/v):=(hp (f a) k').trans (mul_le_mul_of_nonneg_right k (by positivity))
 rw [show linkZ G (g.penalty*a^2)= S.penaltyZ b G from ?_,Real.log_mul (by positivity : a^ (Module.finrank ℝ G.Color)≠0) (S.penaltyZ_pos ..).ne', Real.log_pow,show Real.log a=_ from Real.log_sqrt h.le, he] at k
 · rw [spare_formula _ p.scale h,← shadowLie]; apply (le_of_eq _).trans (k.trans_eq _); unfold halfLie; ring_nf; -- tune
   change C/Real.sqrt b*_= _; ring
 exact heq.symm.trans (by rw [Real.sq_sqrt h.le])
end Fineness
end YM.CF.Py.Rate

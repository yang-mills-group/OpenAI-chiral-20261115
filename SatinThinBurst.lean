import YM.SU5.Fineness.Inches
import SatinThinFlurry
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
/-! # Link normalizer and sharp rooted cable widths. -/
namespace Fineness
open Pannier YM.Fineness
open YM.SectorNext.Vacuum (narrow linkZ narrow_pos mouth first_asymptotic)
variable {G:Gauge}(J':ChartRatio G)(p:LocalRatio J')(ε:ℝ)
set_option linter.unusedVariables false
local notation "r'"=> Fintype.card G.ColorIndex
local notation "d'"=> halfLie G
include p
lemma merit_fare(g:KernelChoices) : ∃ C> (0:ℝ),∀ᶠ b:ℝ in atTop,∀ {m n:Side}(S:StepData m n), S.kernel=g →
 |Real.log (S.penaltyZ b G)-Real.log (spare J' b)+halfLie G *Real.log g.penalty| ≤ C/Real.sqrt b:=by
 let t:=g.penalty; have u:=g.penalty_pos
 let v:=narrow J' t; have ht:=narrow_pos J' p _ u
 have he:Real.log v=logFlat J' - d'*Real.log g.penalty:=by
    have hp : (Real.pi / (t/2))>0:= div_pos Real.pi_pos (half_pos u)
    rw [show v=J'.scale * (Real.pi / (t/2)) ^ d' from rfl, Real.log_mul p.scale.ne' (Real.rpow_pos_of_pos hp _).ne',Real.log_rpow hp]
    rw [show Real.pi/(t/2)= (2*Real.pi)/g.penalty from by unfold t; ring,Real.log_div (mul_pos (by norm_num) Real.pi_pos).ne' u.ne', shadowLie]; unfold logFlat; ring
 let f (x:ℝ):= x^(Module.finrank ℝ G.Color)*linkZ G (g.penalty*x^2)
 have hf:Tendsto (fun x=>|Real.log (f x)-Real.log v|) atTop (𝓝 0):=by simpa only [v,t,sub_self,abs_zero] using (((first_asymptotic J' p _ u).log ht.ne').sub_const (Real.log v)).abs
 obtain ⟨C,hc,F⟩:= YM.SectorNext.Vacuum.first_laplace_receipt J' p t u
 refine ⟨C,hc,?_⟩
 filter_upwards [eventually_gt_atTop (0:ℝ),Real.tendsto_sqrt_atTop.eventually F] with b h k
 intro m n S hS
 let a:=Real.sqrt b
 have h0: 0<a:= Real.sqrt_pos.mpr h
 have heq : S.penaltyZ b G = linkZ G (g.penalty*b) := by
   unfold StepData.penaltyZ StepData.penaltyWeight linkZ SectorNext.Vacuum.mouth
   rw [hS]; congr 1; ext x; ring_nf
 rw [← Real.sq_sqrt h.le] at heq
 change |Real.log (a^ (Module.finrank ℝ G.Color)*linkZ G (g.penalty*a^2))-Real.log v|≤ C/a at k
 rw [show linkZ G (g.penalty*a^2)= S.penaltyZ b G from ?_,Real.log_mul (by positivity : a^ (Module.finrank ℝ G.Color)≠0) (S.penaltyZ_pos ..).ne', Real.log_pow,show Real.log a=_ from Real.log_sqrt h.le, he] at k
 · rw [spare_formula _ p.scale h,← shadowLie]; apply le_trans (le_of_eq _) k; unfold halfLie; ring_nf
 exact heq.symm.trans (by rw [Real.sq_sqrt h.le])

omit p
local notation "G5"=>SU.group

lemma merit_economy(L:Side)(u:ℝ)(p₀:0<u)(Q:ChartRatio SU.group)(v:LocalRatio Q)(K:KernelChoices): ∀ᶠ x:ℝ in atTop,∀ b:ℝ, Scales.y G5 L x/2 ≤ b→∀ {m n:Side}(S:StepData m n), S.kernel= K→ |Real.log (S.penaltyZ b G5)-Real.log (spare Q b) + halfLie G5 *Real.log K.penalty| ≤ u* merit L x := by
 obtain ⟨C,hp,k,g⟩:= (show (∃ C > (0:ℝ), ∃ k,∀ b, k≤b → ∀ {m n:Side}(S:StepData m n), S.kernel= K→ |Real.log (S.penaltyZ b G5)-Real.log (spare Q b)+ halfLie G5*Real.log K.penalty|≤ C/Real.sqrt b) from by simpa only [eventually_atTop] using merit_fare Q v K)
 filter_upwards [Scales.year G5 L|>.eventually_ge_atTop (2*k), Scales.year G5 L|>.eventually_gt_atTop 0,merit_size L u p₀ _ ((sizeK.main L).scale (2*C))] with x t ht u' b t'; intro m n S h
 let f:= Scales.y G5 L x; let F:= Real.sqrt f
 have hv: 0<f:= ht; have hv':0<b:= lt_of_lt_of_le (half_pos ht) t'; let P:=Real.sqrt b; have hF:0<F:= Real.sqrt_pos.mpr hv; have hP:0<P:=Real.sqrt_pos.mpr hv'
 have hx: F ≤ 2*P:= by nlinarith only [Real.sq_sqrt hv.le,Real.sq_sqrt hv'.le,t',hF,hP]
 calc _ ≤ _:= g b (by linarith only [t,t']) S h
      _ ≤ (2*C)/F:= (div_le_div_iff₀ hP hF).mpr (by nlinarith only [mul_le_mul_of_nonneg_left hx hp.le])
      _ ≤ _ := ((le_abs_self (2*C*F⁻¹)).trans u').trans' (le_of_eq (div_eq_mul_inv ..))

lemma wind_merit (L:Side)(u:ℝ)(p₀:0<u)(Q:ChartRatio SU.group)(p':LocalRatio Q)(M:ℝ)(h:0<M):∀ᶠ x:ℝ in atTop,∀ y:ℝ,M*Scales.p G5 L x ≤ y → ∀ b> (0:ℝ),|Real.log (shotM Q y b)-Real.log (spare Q b)|≤ u* merit L x:= by
 obtain ⟨C,hC,K⟩:= Appel.flurry_mass SU.group
 let T (x):=M*Scales.p G5 L x
 obtain ⟨k,hk⟩:= eventually_atTop.mp ((arc_guard G5).eventually (le_mem_nhds (by norm_num:(1/2:ℝ)<1)))
 filter_upwards [(Tendsto.const_mul_atTop h (Scales.peak G5 L)).eventually_ge_atTop k,shot_sight L (M^2/4) C (by positivity) hC (u/2) (half_pos p₀)] with x v ht y hv b t
 have hp₀:0<T x:=mul_pos h (Scales.pos ..); have hy:0<y:= hp₀.trans_le hv
 unfold shotM; rw [Real.log_mul (spare_pos Q p' t).ne' (Appel.point_p hy|>.ne'),add_sub_cancel_left]
 have he:= SectorNext.Vacuum.log_charge (L:=1/2) (by norm_num) (hk y (v.trans hv)) (le_of_lt (by norm_num:(1/2:ℝ)<1))
 rw [Real.log_one,sub_zero,abs_sub_comm (point ..),abs_of_nonneg (K y hy).1] at he
 let B:= Real.exp (-y^2/4); let f:=Scales.p G5 L x
 have hB:1-point G5 y ≤ u/2* merit L x:= calc
    _ ≤ C*B := (K y hy).2
    _ ≤ _:= le_trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (by nlinarith only [pow_le_pow_left₀ (show 0 ≤ M* Scales.p G5 L x from hp₀.le) hv 2])) hC.le) ht
 rw [one_div,div_inv_eq_mul] at he; linarith only [he,hB]

end Fineness
end YM.CF.Py.Rate

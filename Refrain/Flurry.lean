import YM.SU5.Fineness.Inches
import Refrain.Kernel

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
open Pannier YM.Fineness Gaussian ProbabilityTheory
open YM.SectorNext.Vacuum
open scoped ENNReal
local notation "Gfl"=> SU.group
abbrev vSnow := SU.group.Color
def ski (x:vSnow) := Real.exp (‖x‖^2/4)
lemma ski_int : Integrable ski (rice Gfl):=by
 rw [Appel.perk,integrable_withDensity_iff (by unfold peakG; fun_prop) (by simp)]
 let b:ℝ:= 4⁻¹; let v:ℝ:= (Gaussian.dome SU.group.ColorIndex)⁻¹
 have hp (x:SU.group.Color):0≤peakG Gfl x:= (mul_pos (inv_pos.mpr dome_pos) (Real.exp_pos _)).le
 simp_rw [ENNReal.toReal_ofReal (hp _)]
 have h: (fun x:SU.group.Color=> ski x*peakG Gfl x)= fun x=> v*SectorNext.Vacuum.frost b x:= by funext x; unfold peakG ski SectorNext.Vacuum.frost v b; rw [mul_left_comm,←Real.exp_add]; ring_nf
 first | rw [h] | skip
 exact (tint_frost (G:=Gfl) (a:=b) (by norm_num [b])).const_mul _
lemma snow_worth :∃ C> (0:ℝ),∀ t≥ (0:ℝ),1-Appel.point Gfl t ≤ C*Real.exp (-(t^2/4)):=by
 let r:=rice Gfl
 letI:IsProbabilityMeasure r:= by unfold r; infer_instance
 let F:=fun t:ℝ=> closedBall (0:vSnow) t
 let c:= ∫ x,ski x ∂r
 refine ⟨|c|+1,by positivity,fun t ht=>?_⟩
 let Q:ℝ:=Real.exp (t^2/4)
 have hp:0<Q:=Real.exp_pos _
 let B:=F t
 have hm:MeasurableSet B:=isClosed_closedBall.measurableSet
 have hs:(1-Appel.point Gfl t)*Q ≤ ∫ x,ski x ∂r:=by
    have h0: (∫ _x:vSnow in Bᶜ,Q∂r)=(1-Appel.point Gfl t)*Q:=by
       rw [setIntegral_const,smul_eq_mul, measureReal_compl hm,probReal_univ]
       rfl
    rw [←h0]; refine (setIntegral_mono_on (μ:=r) integrableOn_const ski_int.integrableOn hm.compl (fun x h=> ?_)).trans (setIntegral_le_integral ski_int (Eventually.of_forall (fun x=> (Real.exp_pos _).le)))
    have hv:t<‖x‖:=lt_of_not_ge (by intro u; apply h; exact mem_closedBall.mpr (by rwa [dist_zero_right]))
    exact Real.exp_le_exp.mpr (by nlinarith only [pow_le_pow_left₀ ht hv.le 2])
 calc
    _ ≤ (|c|+1)/Q:= (le_div_iff₀ hp).mpr (hs.trans ((le_abs_self c).trans (by linarith)))
    _ = _:= by unfold Q; rw [div_eq_mul_inv,← Real.exp_neg]
end Fineness
end YM.CF.Py.Rate

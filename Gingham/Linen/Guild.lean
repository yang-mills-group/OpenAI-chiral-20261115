import Gingham.Linen.Olive
import YM.CF.Sere.Gilt
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Linen
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Ione


variable {x:ℝ} (L:Side)
open Py
abbrev notch (x:ℝ):= Real.exp ((Real.log (Real.log x))^2)
abbrev stiffness (L:Side) (x:ℝ) := (SectorNext.Remainder.Scales.g SU.group L x)^2 * notch x
local notation "Gy"=> SectorNext.Remainder.Scales.y SU.group L
local notation "Gx"=> SectorNext.Remainder.Scales.g SU.group L

lemma high_price: ∀ᶠ x:ℝ in atTop,
    Real.exp (-1/4*(radiusB x:ℝ)) ≤ stiffness L x ∧ dleaf L x ≤2*stiffness L x ∧
           (Gx x)^2 ≤1:=by
 let a:=SU.group.slopeConstant * Real.log L.val
 filter_upwards [(year SU.group L).eventually_ge_atTop 1,tail_delay SU.group L (1/4) (by norm_num),
         eventually_gt_atTop (0:ℝ),eventually_ge_atTop a] with x y t u j
 have hh:0 < Gy x:=zero_lt_one.trans_le y
 have h₀: 0 < Gx x:= SectorNext.Remainder.Scales.gauge SU.group L hh
 have hy:= yg2 SU.group L hh
 have hv:(Gx x)^2=(Gy x)⁻¹:=eq_inv_of_mul_eq_one_left (mul_comm ..|>.trans hy)
 have m:=Real.one_le_exp (sq_nonneg (Real.log (Real.log x)))
 refine ⟨le_trans ?_ (le_mul_of_one_le_right (sq_nonneg (Gx x)) m),?_,hv.trans_le (inv_le_one_of_one_le₀ y)⟩


 · rw [hv]; refine le_trans ?_ t; apply Real.exp_le_exp.mpr; rw [neg_div]; exact mul_le_mul_of_nonpos_left (by exact_mod_cast Nat.div_le_self (radiusB x) 100000) (by norm_num)
 ·   let b:=Gx x
     rw [stiffness,dleaf,temp]
     change b * ((Real.sqrt x)⁻¹ * notch x) ≤ 2*(b^2*notch x)
     rw [←mul_assoc, ←mul_assoc]
     apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
     have hs: Real.sqrt (Gy x) ≤ 2*Real.sqrt x:=by
        have hz : Gy x ≤ 2*x:=by change x+a≤ _; linarith only [j]
        nlinarith [Real.sq_sqrt hh.le,Real.sq_sqrt u.le,Real.sqrt_nonneg x]
     have h: (Real.sqrt x)⁻¹ ≤ 2*b:=by
        rw [inv_le_iff_one_le_mul₀ (Real.sqrt_pos.mpr u)]
        calc
         _ ≤ Real.sqrt (Gy x)*b := le_of_eq (mul_inv_cancel₀ (Real.sqrt_pos.mpr hh).ne').symm
         _ ≤ _ := (mul_le_mul_of_nonneg_right hs h₀.le).trans_eq (by ring)
     exact (mul_le_mul_of_nonneg_left h h₀.le).trans_eq (by ring)


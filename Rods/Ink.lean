import Rods.Plain
import Rods.Campaign
import YM.SU5.FiniteGaugeData.Pannier.Sketch
set_option autoImplicit false
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
open Ione Beau Haro Cascade Fief VolumeRate
open Roots Buffered LocalLimit LocalLimit.Papal Dyad Dyad.Keeping Mew Compass Drift
attribute [-instance] instDecidableEqLex
set_option quotPrecheck false
open Buffered Advance Afterglow YM.CF.Pannier.Chancel
namespace Decaf
open Stencil Push.SectorMeasure Larch
variable {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}{V:Grace K R L}{e kL:ℝ}{B:Side}{P:Grasp V.U B e}{qχ:Chi}(A:SiteLedger V P kL qχ){φ:Vxpert V A}{D0 f v D Q U:ℕ}(J:PaperTrace V A f v φ D0)(S:Tickets V D0 D Q R.L A f v)(h:Margin R.L D0 D Q U)
variable {n:Side}
open YM.StressFlux AnalyticBridge.VerifiedReset Lattice.PlaqAxes
-- W threshold-dependent upper even w/o flags. norm class open Matrix.Norms.L2Operator but gauge Frobenius side needs instance. Color type has standard
private lemma pcost:∃ c:ℝ,0 ≤ c ∧ ∀ (n:Side)(R:Pane n)(x:Site (More n))(b:PlaqAxes), ‖petals R x b‖≤c:=by
 obtain ⟨c,h⟩:= (isCompact_range (f:=fun u:SU.group.El=>‖SU.group.curvature u‖) (by fun_prop)).bddAbove
 refine ⟨max 0 c,le_max_left ..,fun n R x b=>?_⟩; let D:=max 0 c
 have ht(v w:Lattice.Step): ‖StressFlux.plate (G:=SU.group) R x v w‖ ≤ D:= (h ⟨_,rfl⟩).trans (le_max_right ..)
 unfold AnalyticBridge.VerifiedReset.petals clover StressFlux.stencil
 rw [norm_smul, Real.norm_eq_abs]; rw [abs_of_nonneg (show 0≤ (4:ℝ)⁻¹ by positivity)]
 set i:= b.val.1; set j:= b.val.2
 let v:=StressFlux.plate (G:=SU.group) R x; let A:=v (posDir i) (posDir j); let B:=v (posDir i) (negDir j);let C:=v (negDir i) (posDir j); let D':=v (negDir i) (negDir j)
 change 4⁻¹*‖A-B-(C-D')‖≤D
 have hp:=norm_sub_le (A-B) (C-D'); have hu:=norm_sub_le A B; have hu':=norm_sub_le C D'
 linarith only [hp,hu,hu',(show ‖A‖≤D from ht ..),(show ‖B‖≤D from ht ..),(show ‖C‖≤D from ht ..),(show ‖D'‖≤D from ht ..)]
noncomputable abbrev pcH(p:BudgetPoint)(q:ℝ):ℝ:=(∑ b:PlaqAxes,|q*((decor b):ℝ)/p.threshold^2| *pcost.choose^2)/2
lemma pc_pos(p:BudgetPoint)(q:ℝ):0≤ pcH p q:=by unfold pcH; exact div_nonneg (Finset.sum_nonneg fun i _=>mul_nonneg (abs_nonneg _) (sq_nonneg _)) two_pos.le
lemma inkwell(p:BudgetPoint)(q:ℝ)(o:Site n):SoloC (cameo o p q) (pcH p q):=by
 refine ⟨tariffB o p q,fun _=>rfl,fun x=>?_⟩
 unfold tariffB; split; swap; · rw [abs_zero]; exact pc_pos ..
 unfold Inkprice pcH; rw [abs_div,show |(2:ℝ)|=2 by norm_num]; refine div_le_div_of_nonneg_right ((Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun i _=>?_)) two_pos.le
 rw [abs_mul,abs_of_nonneg (sq_nonneg (‖AnalyticBridge.VerifiedReset.petals x (node o) i‖))]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (pcost.choose_spec.2 _ ..) _) (abs_nonneg _)
lemma solo_far{F:Mark n}{b:ℝ}(a:SoloC F b){t}: ‖F t‖≤ b:=by obtain ⟨⟨r,q,u⟩⟩:=a; rw [q,norm_smul,Complex.norm_real,Real.norm_eq_abs,norm_one,mul_one]; exact u _
#print axioms inkwell
end Decaf
end YM.CF.Py.Rate
end

import YM.CF.Song.Jags
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour.Axial
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
open Haro Ione Larch Glyph
section
variable {N:Side}
end
open Exa Tap Dial
abbrev Tiles:= Fin (Module.finrank ℝ SpaceM)
def markB := Module.finBasis ℝ SpaceM
def rankV (i:Tiles): SpaceM:= ‖markB i‖⁻¹ • (markB i)
def cloth (i:Tiles): SpaceM→L[ℝ]ℝ:= ‖markB i‖ • LinearMap.toContinuousLinearMap (markB.coord i)
def cQ:ℝ:= 1+∑ i:Tiles,‖cloth i‖
lemma cQ_one : 1≤cQ:=le_add_of_nonneg_right (sum_nonneg (fun (i:Tiles) _=> ContinuousLinearMap.opNorm_nonneg _))
lemma cQ_p : 0<cQ:= zero_lt_one.trans_le cQ_one
lemma rank_unit (i:Tiles):‖rankV i‖=1:=by rw [rankV,norm_smul,Real.norm_of_nonneg (by positivity), inv_mul_cancel₀]; exact ne_of_gt (norm_pos_iff.mpr (markB.ne_zero _))
lemma cloth_eq (Q:SpaceM) : ∑ i:Tiles,cloth i Q • rankV i= Q :=by
 have e(i:Tiles): cloth i Q • rankV i=markB.coord i Q • markB i:=by
    unfold rankV; change (‖markB i‖ * _) • _ = _; rw [smul_smul]; refine congrArg (· • (markB i)) ?_; change ‖markB i‖*markB.coord i Q * _= _; rw [mul_comm ‖_‖,mul_assoc,mul_inv_cancel₀ (ne_of_gt (norm_pos_iff.mpr (markB.ne_zero i))),mul_one]
 simp_rw [e]; exact markB.sum_repr Q
lemma cloth_b (Q:SpaceM) : (∑ i:Tiles, ‖cloth i Q‖) ≤ cQ*‖Q‖:=by
 unfold cQ; rw [add_mul,one_mul,sum_mul]; exact (sum_le_sum (fun i _=> (cloth i).le_opNorm _)).trans (le_add_of_nonneg_left (norm_nonneg _))
def stitch {X:Type*}[AddCommGroup X][Module ℝ X](F:Tiles→X) : SpaceM→ₗ[ℝ]X:=∑ i:Tiles,(cloth i).toLinearMap.smulRight (F i)
lemma sit {X:Type*}[AddCommGroup X][Module ℝ X](F:Tiles→X)(Q:SpaceM) : stitch F Q=∑ i,cloth i Q • F i:=by rw [stitch,LinearMap.sum_apply]; rfl
scoped instance garden_one : Nonempty (ΘS 1) :=⟨⟨0,by simp⟩⟩
def pole (i:Tiles):ΘS 1:=⟨rankV i,(rank_unit i).le⟩
end YM.CF.Sour.Axial

import YM.CF.Song.Jags
import YM.CF.Song.Agape
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour.Heath
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
open Exa Tap Dial
open Levier Thera Urn Nacre Salt
open Haro -- 
namespace Cad
abbrev Θ:Type := SpaceM
abbrev Θq := ΘS
abbrev Index := Fin (Module.finrank ℝ Θ)
def BasisQ := Module.finBasis ℝ Θ
-- normalize real unit
lemma length (i:Index) : 0 < ‖BasisQ i‖:= norm_pos_iff.mpr (Module.Basis.ne_zero (BasisQ) i) -- tune
abbrev Expr: Index→Θ:= fun i=> ‖BasisQ i‖⁻¹ • BasisQ i
lemma normE (i:Index): ‖Expr i‖=1:= by unfold Expr; rw [norm_smul,norm_inv,norm_norm,inv_mul_cancel₀ (length i|>.ne')]
abbrev unitCell(i:Index): Θq 1:=⟨Expr i,(normE i).le⟩
lemma nonzero{v:ℝ}(p:0≤v): Nonempty (ΘS v):=⟨0,by rw [norm_zero]; exact p⟩ -- tune syntax subtype
abbrev econ(i:Index): Θ→L[ℝ] ℝ:= ‖BasisQ i‖ • (BasisQ.coord i).toContinuousLinearMap
def rent := max 1 (∑ i:Index,‖econ i‖)
lemma tagline (q:Θ) : ∑ i:Index,econ i q • Expr i=q:=by apply Eq.trans _ (BasisQ.sum_repr q); refine sum_congr rfl ?_; intro i _; change (‖BasisQ i‖ * (BasisQ.repr q i)) • (‖BasisQ i‖⁻¹ • BasisQ i)= _; rw [smul_smul,mul_comm ‖BasisQ i‖,mul_assoc,mul_inv_cancel₀ (length i|>.ne'),mul_one]
lemma rent_p : 1 ≤ Cad.rent:= le_max_left ..
lemma pos : 0 < Cad.rent := zero_lt_one.trans_le rent_p
lemma horizon (q:Θ): (∑ i:Index, |econ i q|) ≤ rent*‖q‖:= (sum_le_sum (fun i _=> ((econ i).le_opNorm q))).trans (by rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _)) -- arg annotation
end Cad
end YM.CF.Sour.Heath

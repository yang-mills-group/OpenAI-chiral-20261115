import YM.CF.Pic.Firm
import YM.CF.BProof.Chord

/-! Conversions: Op argument distances can include both matter and fundamental!
Corresponding chord prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Spin
open Function Filter Fock ExTwo Finset Branch SU Cube Tulip Tenant Lattice Lat
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace
local notation "G"=> SU.group
-- adapted Nova.Era.boundedFrame, avoid deps
open scoped Matrix.Norms.Frobenius in
lemma fund_bill(u:E)(i j:SU.F): ‖fund u i j-(1:Op SU.F) i j‖≤ SU.group.colorScale * SU.group.chord u:=by
 unfold Gauge.chord; rw [show (SU.group.colorScale * (‖SU.group.mat u-1‖/Real.sqrt SU.group.repDim))= ‖SU.group.mat u-1‖ from mul_div_cancel₀ _ SU.group.colorScale_pos.ne'] -- tune
 let A:=fund u-1; change ‖A i j‖≤‖A‖; apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1; rw [Gauge.frob_sq]
 have he:(A*star A).trace.re= ∑ i:SU.F,∑ j:SU.F,‖A i j‖^2:=by unfold Matrix.trace; simp only [Complex.re_sum,Matrix.diag_apply,Matrix.mul_apply]; exact sum_congr rfl fun i _=> sum_congr rfl fun j _=> inner_self_eq_norm_sq (𝕜:=ℂ) (A i j)
 rw [he]; exact le_trans (single_le_sum (f:=fun j=> ‖A i j‖^2) (fun j _=>sq_nonneg _) (mem_univ _)) (single_le_sum (f:=fun i=>∑ j, ‖A i j‖^2) (fun i _=> sum_nonneg fun _ _=>sq_nonneg _) (mem_univ _))
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
def scenery (u v:E) := ‖brand u-brand v‖
lemma seen (u v:E) : scenery u v= max (Cube.cmp matter u v) (Cube.cmp firstF u v):=rfl
lemma viewCost : ∃ K:ℝ, 1≤K ∧ (∀ u v:E,scenery u v ≤ K * cd G u v) ∧ ∀ u v:E,cd G u v ≤ K*scenery u v:=by
 have he:=(show 0<SU.group.colorScale from SU.group.colorScale_pos); have hx(u v:E): Cube.cmp firstF u v≤5*SU.group.colorScale*cd G u v:=by
    rw [← cmp_left firstF u v u⁻¹,inv_mul_cancel,Cube.cmp_sym]; let g:=u⁻¹*v; change ‖fund g-1‖≤5*SU.group.colorScale*SU.group.chord g; exact (Sods.cost_D _ (E:=SU.F) (fund_bill g) (mul_nonneg he.le (SU.group.chord_nonneg _))).trans_eq (by simp [F]; ring)
 obtain ⟨k,h,H⟩:= Pic.gulf; obtain ⟨l,g,L⟩:= Pic.zeta
 let m:=k*(5*SU.group.colorScale); have hv:0<k:=zero_lt_one.trans_le h; refine ⟨max 1 (max m l),le_max_left ..,fun u v=>?_,fun u v=>?_⟩
 · apply le_trans (b:= m*cd G u v); rw [seen]; apply max_le; exact (H u v).trans ((mul_le_mul_of_nonneg_left (hx u v) hv.le).trans_eq (mul_assoc ..).symm); rw [show m=_ from rfl]; exact (hx u v).trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by positivity : 0≤5*SU.group.colorScale) h) (cd_nonneg ..)); exact mul_le_mul_of_nonneg_right ((le_max_left m l).trans (le_max_right ..)) (cd_nonneg ..) -- tune one-line
 apply le_trans (L (u⁻¹*v) (Cube.cmp firstF u v) ?_); · rw [seen]; exact mul_le_mul ((le_max_right m l).trans (le_max_right ..)) (le_max_right ..) (norm_nonneg _) (by exact zero_le_one.trans (le_max_left ..))
 intro i j; rw [←cmp_left firstF u v u⁻¹] -- tune
 rw [inv_mul_cancel,Cube.cmp_sym]; exact norm_entry (fund (u⁻¹*v)-1) i j
end YM.CF.BProof.Spin

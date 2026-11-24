import YM.SU5.FiniteGaugeData.Stent.Quint
/-! Torque gains. actual Petri telescope L^-1/2 EXP, no link hypotheses! -/
set_option autoImplicit false
set_option maxHeartbeats 380000
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.Buffered.Stent.Purchase
open Function Filter Finset Lattice Laurent Fir Next.Free Bloch Lat Fock Rush Scroll MeasureTheory RG
open scoped Topology BigOperators Pointwise Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace Kronecker ENNReal
attribute [local instance] opCStarAlgebra
variable (R:Patch)
set_option quotPrecheck false
local notation "Λ"=> R.L
local notation "J"=> R.J
open Cube Stencil Tenant Tap Tulip Branch Spire Peaks Advance Skye Lifted CF.Stent
variable {x:Cover}
open NormedSpace
variable {N: Side}{b:Bool}{F:Op SU.Slot}
local notation "Ω"=> Op SU.Slot
variable {ι κ ν:Type*}[LinearOrder κ] [Fintype κ] [LinearOrder ι][Fintype ι][LinearOrder ν][Fintype ν]
def lockPrice : ℝ:= ∑ i:SpinIdx, ‖(Aop-(1/2:ℂ) • (1:Op SpinIdx)) i i‖
-- cf.Graph.bootC
private lemma lockBill (a:Ω): ‖exp a‖≤Real.exp ‖a‖:=by
 rw [congrFun (exp_eq_tsum ℝ), Real.exp_eq_exp_ℝ,congrFun (exp_eq_tsum ℝ)]
 refine (norm_tsum_le_tsum_norm (norm_expSeries_summable' (𝕂:=ℝ) a)).trans ?_
 exact Summable.tsum_mono (norm_expSeries_summable' (𝕂:=ℝ) a) (by apply Summable.of_norm; exact norm_expSeries_summable' (𝕂:=ℝ) ‖a‖) (fun n=> by rw [norm_smul,Real.norm_of_nonneg (by positivity)]; exact mul_le_mul_of_nonneg_left (norm_pow_le ..) (by positivity))
lemma dances (i:SpinIdx) : ‖Lock F b i‖ ≤ Real.exp (lockPrice*‖F‖):=by
 unfold Lock; split
 next e=> refine (lockBill _).trans (Real.exp_monotone ?_); rw [PlusM,norm_smul]; exact mul_le_mul_of_nonneg_right (single_le_sum (f:=fun i:SpinIdx=> ‖(Aop-(1/2:ℂ) • (1:Op SpinIdx)) i i‖) (fun i _=>norm_nonneg _) (mem_univ i)) (norm_nonneg _)
 next e=> refine (lockBill _).trans (Real.exp_monotone ?_); rw [norm_neg,PlusM,norm_smul]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); exact single_le_sum (f:=fun i:SpinIdx=> ‖(Aop-(1/2:ℂ) • (1:Op SpinIdx)) i i‖) (fun i _=>norm_nonneg _) (mem_univ i)
lemma fee_price (v:Ket (Single N)): ‖acts (feeL b N F) v‖ ≤ Real.exp (lockPrice*‖F‖)*‖v‖:= by
 refine (Flare.opy (feeL b N F) v).trans ?_
 apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
 rw [feeM]; exact jump_bound _ _ (Real.exp_nonneg _) (fun i=> dances i.2)
#print axioms fee_price
end YM.CF.Buffered.Stent.Purchase

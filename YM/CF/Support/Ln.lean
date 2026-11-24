import YM.CF.Support.Gust
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Local log bills as power series with kernel-valued terms. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Branch
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Finset Function Fock Filter NormedSpace MeasureTheory
attribute [local instance] opCStarAlgebra
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
def bcoef (n : ℕ) : ℝ := ∫ t in (0:ℝ)..1, (-t)^n
lemma bc_norm (n) : ‖bcoef n‖≤1 := by
  unfold bcoef; convert! intervalIntegral.norm_integral_le_of_norm_le_const (a:=(0:ℝ)) (b:=(1:ℝ)) (C:=1) ?_ using 1
  · simp
  intro x hx; rw [norm_pow,norm_neg]; apply pow_le_one₀ (norm_nonneg _); rw [Set.uIoc_of_le zero_le_one] at hx; rw [Real.norm_of_nonneg hx.1.le]; exact hx.2

def pencil (A : Op I) := ∑' n:ℕ, bcoef n • A^(n+1)
lemma tally_log {A : Op I} (h : ‖A‖<1) : invoice A=(pencil A).trace := by
  let L : Op I →L[ℝ] ℂ :=
    { Matrix.traceLinearMap I ℝ ℂ with
      cont := continuous_id.matrix_trace }
  have hl (B : Op I) : L B=B.trace := rfl
  let b (t:ℝ) := (-t) • A
  let F : ℕ → C(ℝ, ℂ) := fun n=> ⟨fun t=> L ((-t)^n • A^(n+1)),L.continuous.comp (by fun_prop)⟩
  let v := ‖A‖; have hp : 0≤v := norm_nonneg _
  have hb (t:ℝ) (ht:t∈ Set.uIcc 0 1) : ‖-t‖≤1 := by rw [Set.uIcc_of_le zero_le_one] at ht; simp [Real.norm_of_nonneg ht.1, ht.2]
  have he (t:ℝ) (ht:t∈ Set.uIcc 0 1) : Fock.slope A t=∑' n,F n t := by
    have hx : ‖b t‖ ≤ v := by unfold b; rw [norm_smul]; exact (mul_le_mul_of_nonneg_right (hb t ht) hp).trans (le_of_eq (one_mul _))
    rw [Fock.slope, ←hl,beam, show 1+(t:ℂ) • A=1-b t by unfold b; rw [neg_smul,sub_neg_eq_add]; congr 1]
    have hs := summable_geometric_of_norm_lt_one (hx.trans_lt h)
    rw [←route_inv (hx.trans_lt h), ← hs.tsum_mul_right, L.map_tsum (hs.mul_right A)] -- tune
    apply tsum_congr; intro i; change L (b t^i*A)=L ((-t)^i • A^(i+1)); unfold b; rw [smul_pow,Algebra.smul_mul_assoc, ←pow_succ]
  let W : TopologicalSpace.Compacts ℝ := ⟨Set.uIcc 0 1,isCompact_uIcc⟩
  let c := fun n:ℕ=> v^(n+1)
  have hC : Summable c := (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hp h)
  have hu : Summable (fun i=>‖(F i).restrict (W:Set ℝ)‖) := by
    apply (hC.mul_left ‖L‖).of_nonneg_of_le (fun _=> norm_nonneg _); intro n
    apply (ContinuousMap.norm_le _ (by unfold c; positivity)).mpr; intro t
    change ‖L ((-t.val)^n • A^(n+1))‖≤_
    apply (L.le_opNorm _).trans; rw [norm_smul,norm_pow]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hb t.val t.property))).trans (norm_pow_le ..)
  have hy : Summable (fun n:ℕ=>bcoef n • A^(n+1)) := by
    apply hC.of_norm_bounded; intro n; rw [norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) (bc_norm _)).trans (norm_pow_le ..)
  rw [invoice,intervalIntegral.integral_congr he, ←intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hu, pencil, ← hl, L.map_tsum hy]
  apply tsum_congr; intro n
  change (∫ t in (0:ℝ)..1,L ((-t)^n • A^(n+1)))=L _
  simp_rw [map_smul]; rw [intervalIntegral.integral_smul_const]; rfl -- tune
end YM.CF.Branch

import YM.CF.Lattice.Symbol
import YM.CF.Matter.Anomaly
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Kinetic symbol linearization (input only). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BZ
open scoped Matrix.Norms.L2Operator Matrix BigOperators Topology
attribute [local instance] opCStarAlgebra
abbrev gPos := (atom 0).plus
def symbolD (v : Mom) := ∑ i, v i • (Complex.I • gammaOp i)
lemma lin_bare (v : Mom) : HasDerivAt (fun t:ℝ => bare (t • v)) 0 0 := by
  have hs (i:Fin 4) : HasDerivAt (fun t:ℝ => 1 - Real.cos (t*v i)) 0 0 := by
    convert (hasDerivAt_const (0:ℝ) (1:ℝ)).sub (((hasDerivAt_id' (0:ℝ)).mul_const (v i)).cos) using 1 <;> first | rfl | simp
  have ht := (hasDerivAt_const (0:ℝ) (-1:ℝ)).add (HasDerivAt.fun_sum (u:=Finset.univ) fun i _ => hs i)
  simp only [Finset.sum_const_zero, zero_add] at ht; exact ht
lemma lin_wave (v : Mom) : HasDerivAt (fun t:ℝ => wave (t • v)) 0 0 := by
  have hs (i:Fin 4) : HasDerivAt (fun t:ℝ => Real.sin (t*v i)^2) 0 0 := by
    convert (((hasDerivAt_id' (0:ℝ)).mul_const (v i)).sin.pow 2) using 1 <;> first | rfl | simp
  have ht := ((lin_bare v).pow 2).add (HasDerivAt.fun_sum (u:=Finset.univ) fun i _ => hs i)
  simp only [Finset.sum_const_zero,add_zero,mul_zero] at ht
  have he := ht.sqrt (by simp [bare]); simp only [zero_div] at he; exact he
lemma lin_slash (v : Mom) : HasDerivAt (fun t:ℝ => slash (t • v)) (symbolD v) 0 := by
  unfold slash symbolD
  apply HasDerivAt.fun_sum
  intro i _
  have ht := (((hasDerivAt_id' (0:ℝ)).mul_const (v i)).sin).smul_const (Complex.I • gammaOp i); simp at ht; exact ht
lemma gradeMinus : grading*gPos = gPos := (atom 0).chirPlus
lemma symbol_gr (v : Mom) : grading*symbolD v = -(symbolD v*grading) := by
  unfold symbolD; rw [Matrix.mul_sum,Matrix.sum_mul,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro i _; simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, gradingSwap, smul_neg]
lemma flip_minus (v : Mom) : gPos*symbolD v=symbolD v*(1-gPos) := by
  have he : gPos = (1/2:ℝ) • (1+grading) := rfl
  rw [he,Algebra.smul_mul_assoc,mul_sub,Algebra.mul_smul_comm,add_mul,mul_add,one_mul,mul_one, symbol_gr]; module

/-- Transport the minus-chirality test columns by projection. The first
order surviving kinetic matrix is the restriction of `i γ·p/2` to them. -/
theorem linear_kinetic (v : Mom) : HasDerivAt
    (fun t:ℝ => ((atom (t • v)).overlap * projector (atom (t • v)).H)*(1-gPos))
    ((1/2:ℝ) • (symbolD v*(1-gPos))) 0 := by
  let L := fun t:ℝ => atom (t • v)
  have he : HasDerivAt (fun t => (L t).H0) (symbolD v) 0 := by
    dsimp only [L]; simp_rw [atom_H0]; have he := ((lin_bare v).smul_const (1 : Op SpinIdx)).add (lin_slash v)
    simp only [zero_smul, zero_add] at he; exact he
  have hh := he.const_mul grading
  change HasDerivAt (fun t => (L t).H) (grading*symbolD v) 0 at hh
  have hf := ((lin_wave v).inv (by simp [wave,bare])).smul hh
  have hy : HasDerivAt (fun t => polarity (L t).H) (grading*symbolD v) 0 := by
    dsimp only [L]; simp_rw [atomS]
    convert! hf using 1
    simp [wave,bare]
  simp_rw [WilsonFrame.overlap_action _ (atom_safe _), projector]
  have hz := ((((hasDerivAt_const (0:ℝ) (1:Op SpinIdx)).add hy).const_smul (1/2:ℝ)).const_mul gPos).mul_const (1-gPos)
  convert! hz using 1
  simp only [zero_add, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← mul_assoc]
  rw [show gPos*grading=gPos from (atom 0).plusChir, flip_minus,mul_assoc, show ((1:Op SpinIdx)-gPos)*(1-gPos)=1-gPos by
    simp only [mul_sub, sub_mul,mul_one,one_mul, (atom 0).plusSq]; abel]
end YM.CF.BZ

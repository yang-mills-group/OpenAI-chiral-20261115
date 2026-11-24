import YM.CF.BProof.Align.Order

/-! `Branch.pencil A` bill for log(1+A); used on positive arguments ≤1 for hole
 conditioning & loss, and <2 for tilted norm. Cost in Functional. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Align
open Function Filter Fock Finset Branch MeasureTheory
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[DecidableEq I][Fintype I][Nonempty I] {A:Op I}
lemma logNorm (h:‖A‖<1): Real.log ‖(1+A).det‖ = (pencil A).trace.re := by rw [← Fock.factor A h, Complex.norm_exp, Real.log_exp, tally_log h]
@[simp] lemma pastel_zero : pencil (0:Op I)=0:=by simp [pencil]
lemma biCoeff (n:ℕ) : bcoef n=(-1)^n* ((n:ℝ)+1)⁻¹:=by unfold bcoef; rw [show (fun x:ℝ=> (-x)^n)=(fun x=> (-1)^n*x^n) from funext fun x=>by rw [←mul_pow]; simp]; rw [intervalIntegral.integral_const_mul,integral_pow]; simp
lemma sumPast (h:‖A‖<1): Summable (fun n:ℕ=> bcoef n • A^(n+1)):= ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) h)).of_norm_bounded (fun n=> by rw [norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) (bc_norm _)).trans (norm_pow_le ..)) -- tune
lemma negPiece (A:Op I)(n:ℕ): bcoef n • ((-A)^(n+1)) = -(((n:ℝ)+1)⁻¹ • A^(n+1)):=by
 rw [biCoeff]; rcases Nat.even_or_odd n with g|g
 · have ht: Odd (n+1):=g.add_odd (by decide); rw [g.neg_one_pow,one_mul,ht.neg_pow,smul_neg]
 have ht:Even (n+1):=g.add_odd (by decide); rw [g.neg_one_pow,neg_one_mul,ht.neg_pow,neg_smul]
lemma negPastel (h:‖A‖<1)(p:0≤A): pencil (-A)≤ -A:=by
 let P (i:ℕ):= bcoef i • (-A)^(i+1); let T:=∑' i,P (i+1); have hx:Summable P:=sumPast (A:=-A) (by rwa [norm_neg]); have hh:0≤ -T:=by
    unfold T; rw [←tsum_neg]; let f(i:ℕ):= -P (i+1); have ht(i):0≤ f i:=by unfold f P; rw [negPiece,neg_neg]; exact smul_nonneg (by positivity) (CStarAlgebra.pow_nonneg p _)
    exact isClosed_le continuous_const continuous_id |>.mem_of_tendsto ((summable_nat_add_iff 1).mpr hx).neg.hasSum.tendsto_sum_nat (Eventually.of_forall fun i:ℕ=>sum_nonneg fun j _=>ht j)
 rw [show pencil (-A)= P 0+T from (by rw [← show ∑ i∈range 1,P i=P 0 by simp]; exact (hx.sum_add_tsum_nat_add 1).symm),show P 0= -A from (by simp [P,bcoef]), add_le_iff_nonpos_right]; exact neg_nonneg.mp hh
open scoped ComplexOrder in
lemma diagonal_le (x y:Op I)(h:x≤y)(i:I): (x i i).re ≤ (y i i).re := by
 suffices he:0≤(y i i - x i i).re by rw [Complex.sub_re] at he; linarith
 exact (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h) |>.diag_nonneg (i:=i)).1 -- check
end YM.CF.BProof.Align

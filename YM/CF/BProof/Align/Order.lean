import YM.CF.Support.Hit
/-! Finite-matrix bounds all in FiniteGaugeData Op norms. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Align
open Function Filter Fock Finset Branch
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I : Type*}[Fintype I][DecidableEq I] {c d k:ℝ}{A : Op I}
lemma betweenNorm (p:0≤c)(h:0≤A)(e:A ≤ c • (1:Op I)): ‖A‖≤c:= (CStarAlgebra.norm_le_iff_le_algebraMap _ p h).mpr (by rwa [Algebra.algebraMap_eq_smul_one])
theorem strictPositive (p:0<c)(h:c • (1:Op I) ≤ A): IsStrictlyPositive A:= by
 apply IsStrictlyPositive.of_le _ h
 exact (live_of (show (c • (1:Op I))*(c⁻¹ • 1)=1 from by rw [Algebra.smul_mul_assoc,one_mul,smul_inv_smul₀ p.ne' _])).isStrictlyPositive (smul_nonneg p.le zero_le_one)
theorem active (p:0<c)(h:c • (1:Op I) ≤ A): IsUnit A:= (strictPositive p h).isUnit
theorem invOrder (p:0<c)(h:c • (1:Op I) ≤ A): A⁻¹ ≤ c⁻¹ • (1:Op I):= by
 have ht:(c • (1:Op I))⁻¹=c⁻¹ • 1:= Matrix.inv_eq_right_inv (by rw [Algebra.smul_mul_assoc,one_mul,smul_inv_smul₀ p.ne'])
 rw [← ht,Matrix.nonsing_inv_eq_ringInverse,Matrix.nonsing_inv_eq_ringInverse]; exact CStarAlgebra.ringInverse_le_ringInverse h (strictPositive p le_rfl)
lemma invPositive (p:0<c)(h:c • (1:Op I) ≤ A): 0 ≤ A⁻¹ := by rw [Matrix.nonsing_inv_eq_ringInverse]; exact (strictPositive p h).ringInverse.nonneg
lemma invNorm (p:0<c)(h:c • (1:Op I) ≤ A): ‖A⁻¹‖ ≤ c⁻¹ := betweenNorm (inv_pos.mpr p).le (invPositive p h) (invOrder p h)
lemma rescale (p:0<c)(q:c≤k)(h:c • (1:Op I) ≤ A)(g:A ≤ k • (1:Op I)) : ‖1-k⁻¹ • A‖≤1-c/k := by
 have hh:=p.trans_le q; have ht:0≤ k⁻¹:=(inv_pos.mpr hh).le
 apply betweenNorm (sub_nonneg.mpr ((div_le_one hh).mpr q)) (sub_nonneg.mpr ((smul_le_smul_of_nonneg_left g ht).trans_eq (inv_smul_smul₀ hh.ne' _)))
 rw [sub_smul,one_smul,div_eq_inv_mul,mul_smul]; exact sub_le_sub_left (smul_le_smul_of_nonneg_left h ht) _
lemma rescale_inv (hk:0<k)(h:IsUnit A): A⁻¹ = k⁻¹ • (k⁻¹ • A)⁻¹ := by
 have he:(k⁻¹ • A)⁻¹=k • A⁻¹ := Matrix.inv_eq_right_inv (by rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm,inv_smul_smul₀ hk.ne',(live h).1])
 rw [he,inv_smul_smul₀ hk.ne' _]
lemma under {p:ℝ}(h:0≤A)(e:‖A‖≤p) : A ≤ p • (1:Op I):= (op_le_norm_one (IsSelfAdjoint.of_nonneg h)).trans (smul_le_smul_of_nonneg_right e zero_le_one)
lemma sized (A : Op I): star A*A ≤ ‖A‖^2 • (1:Op I) := under (star_mul_self_nonneg _) (by simp [CStarRing.norm_star_mul_self,pow_two])
end YM.CF.BProof.Align

import YM.CF.Support.Ln

/-! Power log in the small ball. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Petal
open scoped BigOperators Topology
open Filter NormedSpace Branch MeasureTheory Set
variable {E : Type*} [NormedCommRing E] [NormOneClass E] [NormedAlgebra ℝ E] [CompleteSpace E]
def steam (A : E) := ∑' i:ℕ, bcoef i • A^(i+1)
lemma steam_one {A : E} (h : ‖A‖<1) : exp (steam A)=1+A := by
  let V (t:ℝ) := (-t) • A
  let B (t:ℝ) := 1-V t
  let p (t:ℝ) := Ring.inverse (B t)*A
  let f (t:ℝ) := ∫ x in (0:ℝ)..t, p x
  let S := uIcc (0:ℝ) 1
  let r := ‖A‖; have he t (g:t∈S) : ‖t‖ ≤ 1 := by rw [show S=uIcc 0 1 from rfl,uIcc_of_le zero_le_one] at g; rw [Real.norm_of_nonneg g.1]; exact g.2 -- unfold S
  let T := {x| ‖V x‖ < 1}; have hV : Continuous V := by unfold V; fun_prop
  have hB : Continuous B := continuous_const.sub hV
  have hk : S ⊆ T := fun x hx=> by change ‖(-x) • A‖<_; rw [norm_smul,norm_neg]; exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (he x hx)) h
  have ht : IsOpen T := isOpen_lt hV.norm continuous_const
  have hj x (g:x∈T) : ContinuousAt p x := (((show ContinuousAt Ring.inverse (B x) from NormedRing.inverse_continuousAt (Units.oneSub (V x) g))).comp hB.continuousAt).mul_const _ -- tune
  have hx t (g:t∈S) : HasDerivAt f (p t) t := by
    apply intervalIntegral.integral_hasDerivAt_right _ (ContinuousAt.stronglyMeasurableAtFilter ht hj t (hk g)) (hj t (hk g))
    exact ContinuousOn.intervalIntegrable (fun x l=> (hj x (hk (uIcc_subset_uIcc_left g l))).continuousWithinAt)
  let F : ℕ→ C(ℝ,E) := fun n=> ⟨fun t=>(-t)^n • A^(n+1),by fun_prop⟩
  have hv : steam A=f 1 := by
    have hw t (g:t∈S) : p t=∑' i,F i t := by
      unfold p B; rw [NormedRing.inverse_one_sub _ (hk g)]
      change (∑' n:ℕ, V t^n)*A = _
      rw [← (summable_geometric_of_norm_lt_one (hk g)).tsum_mul_right A]; apply tsum_congr; intro n
      change ((-t) • A)^n*A=(-t)^n • A^(n+1); rw [smul_pow, Algebra.smul_mul_assoc, ←pow_succ]
    unfold f; rw [intervalIntegral.integral_congr hw,←intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm]; swap
    · apply ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) h)).of_nonneg_of_le (fun i=> norm_nonneg _)
      intro n; apply (ContinuousMap.norm_le _ (by positivity)).mpr; intro t
      change ‖(-t.val)^n • A^(n+1)‖ ≤ _; rw [norm_smul,norm_pow]; exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (by rw [norm_neg]; exact he t.val t.property))).trans (norm_pow_le ..)
    apply tsum_congr; intro i; unfold bcoef; exact (intervalIntegral.integral_smul_const _ _).symm
  let D (t:ℝ) := B t*exp (-f t)
  have hD t (g:t∈S) : HasDerivAt D 0 t := by
    have hP : HasDerivAt B A t := by unfold B V; simpa using (((hasDerivAt_id' t).neg.smul_const A).const_sub 1)
    have H := hasFDerivAt_exp.comp_hasDerivAt t (hx t g).neg
    have hh := hP.mul H
    have hf : B t * p t = A := by unfold p; rw [←mul_assoc,Ring.mul_inverse_cancel (B t) (show IsUnit (B t) from Units.isUnit (Units.oneSub _ (hk g))),one_mul]
    convert! hh using 1; change 0=A * exp (-f t)+ B t * (exp (-f t)* -p t) -- tune derivative order
    rw [mul_neg,mul_neg,←mul_left_comm]; rw [hf]; ring
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hD (by simp)
  haveI : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℝ E -- introduced too late?
  simp only [D,f,intervalIntegral.integral_zero, B,V,one_smul,neg_smul, neg_zero,zero_smul,add_zero,sub_neg_eq_add, intervalIntegral.integral_same,exp_zero,mul_one] at heq
  have hl : (1+A)*exp (-f 1)=1 := sub_eq_zero.mp heq.symm
  rw [hv]; nth_rw 1 [← one_mul (exp (f 1)), ←hl]; rw [mul_assoc,←exp_add,neg_add_cancel,exp_zero,mul_one]
end YM.CF.Petal

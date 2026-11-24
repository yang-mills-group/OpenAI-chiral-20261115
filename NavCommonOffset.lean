import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

/-! The common-parameter averaging step in the Nav volume-batch argument. -/
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal BigOperators

namespace SatinContinuumAudit.Nav

/-- With normalized offset measure, if each volume rejects at most one eighth
of the offsets, then at most one quarter of the offsets lose at least half of
the volumes simultaneously. The rejected sets may be fully correlated. -/
theorem rejected_by_half {I X : Type*} [Fintype I] [Nonempty I] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (reject : I → Set X)
    (hm : ∀ i, MeasurableSet (reject i)) (h : ∀ i, μ (reject i) ≤ 1 / 8) :
    μ {x | (Fintype.card I : ℝ≥0∞) / 2 ≤
      ∑ i, (reject i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x} ≤ 1 / 4 := by
  classical
  let f (i : I) := (reject i).indicator (fun _ ↦ (1 : ℝ≥0∞))
  let n : ℝ≥0∞ := Fintype.card I
  have hn : n ≠ 0 := by simp [n, Fintype.card_ne_zero]
  have htop : n ≠ ∞ := by simp [n]
  have hf (i : I) : Measurable (f i) := measurable_const.indicator (hm i)
  have he (i : I) : ∫⁻ x, f i x ∂μ = μ (reject i) := by
    simp [f, lintegral_indicator (hm i)]
  have hsum : ∫⁻ x, ∑ i, f i x ∂μ ≤ n / 8 := by
    rw [lintegral_finsetSum Finset.univ (fun i _ ↦ hf i)]
    calc
      _ ≤ ∑ _i : I, (1 / 8 : ℝ≥0∞) :=
        Finset.sum_le_sum (fun i _ ↦ (he i).le.trans (h i))
      _ = n / 8 := by simp [n, nsmul_eq_mul, div_eq_mul_inv]
  have h0 : n / 2 ≠ 0 := by simp [ENNReal.div_eq_zero_iff, hn]
  have hfin : n / 2 ≠ ∞ := by finiteness
  have hs : Measurable (fun x ↦ ∑ i, f i x) := by fun_prop
  apply (meas_ge_le_lintegral_div hs.aemeasurable h0 hfin).trans
  apply (ENNReal.div_le_div_right hsum _).trans
  rw [ENNReal.div_le_iff h0 hfin]
  simp only [div_eq_mul_inv, one_mul]
  have hc : (8 : ℝ≥0∞)⁻¹ = (4 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ := by
    rw [show (8 : ℝ≥0∞) = 4 * 2 by norm_num]
    exact ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inr (by norm_num))
  rw [hc]
  apply le_of_eq
  ac_rfl

/-- One common offset works for strictly more than half the admitted volumes. -/
theorem exists_common_offset {I X : Type*} [Fintype I] [Nonempty I] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (reject : I → Set X)
    (hm : ∀ i, MeasurableSet (reject i)) (h : ∀ i, μ (reject i) ≤ 1 / 8) :
    ∃ x, (∑ i, (reject i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x) <
      (Fintype.card I : ℝ≥0∞) / 2 := by
  classical
  by_contra! hall
  have bound := rejected_by_half μ reject hm h
  have hu : {x : X | (Fintype.card I : ℝ≥0∞) / 2 ≤
      ∑ i, (reject i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x} = Set.univ :=
    Set.eq_univ_of_forall (fun x ↦ hall x)
  rw [hu, measure_univ] at bound
  have small : (1 / 4 : ℝ≥0∞) < 1 := by
    rw [ENNReal.div_lt_iff (by norm_num) (by norm_num)]
    norm_num
  exact (not_lt_of_ge bound) small

end SatinContinuumAudit.Nav

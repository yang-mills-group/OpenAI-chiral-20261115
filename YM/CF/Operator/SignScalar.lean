import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Ring

/-! Binomial coefficients used in the functional calculus with volume-independent majorant. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.SignScalar
open Finset HasAntidiagonal
open scoped BigOperators

def c : ℕ → ℝ
| 0 => 1
| n+1 => ((n:ℝ)+1/2)/((n:ℝ)+1)*c n
lemma c_step (n : ℕ) : (n+1:ℝ)*c (n+1)=(n+1/2:ℝ)*c n := by
  rw [c]; field_simp
lemma c_nn (n) : 0 ≤ c n := by
  induction n with
  | zero => simp [c]
  | succ n ih => rw [c]; positivity
lemma c_le (n) : c n ≤ 1 := by
  induction n with
  | zero => simp [c]
  | succ n ih =>
    rw [c]
    apply (mul_le_of_le_one_left (c_nn n) ?_).trans ih
    apply (div_le_one (by positivity)).mpr; linarith
lemma c_norm (n) : ‖c n‖ ≤ 1 := by rw [Real.norm_of_nonneg (c_nn n)]; exact c_le n

lemma c_conv (n : ℕ) : ∑ p ∈ antidiagonal n, c p.1*c p.2 = 1 := by
  induction n with
  | zero => simp [c]
  | succ n ih =>
    apply mul_left_cancel₀ (show (n+1:ℝ) ≠ 0 by positivity)
    let x (p : ℕ × ℕ) := (p.1:ℝ)*c p.1*c p.2
    let y (p : ℕ × ℕ) := (p.2:ℝ)*c p.2*c p.1
    calc
      _ = ∑ p ∈ antidiagonal (n+1), (x p+y p) := by
        rw [mul_sum]; apply sum_congr rfl; intro p hp
        have he := mem_antidiagonal.mp hp
        have hh : (p.1:ℝ)+(p.2:ℝ)=(n:ℝ)+1 := by exact_mod_cast he
        rw [← hh]; dsimp [x,y]; ring
      _ = _ := by
        rw [sum_add_distrib, Finset.Nat.sum_antidiagonal_succ (f:=x), Finset.Nat.sum_antidiagonal_succ' (f:=y),
          show x (0,n+1)=0 by simp [x], show y (n+1,0)=0 by simp [y], zero_add,zero_add, ← sum_add_distrib]
        conv_rhs => rhs; rw [← ih]
        rw [mul_sum]; apply sum_congr rfl; intro p hp
        dsimp only [x,y]; push_cast; rw [c_step,c_step]
        have he : (p.1:ℝ)+(p.2:ℝ)=(n:ℝ) := by exact_mod_cast mem_antidiagonal.mp hp
        rw [← he]; ring -- rewrites occurrences of n only

def bin (r : ℝ) := ∑' k, c k * r^k

lemma bin_summable (r : ℝ) (hr : ‖r‖ < 1) : Summable (fun k => ‖c k * r^k‖) := by
  apply (summable_geometric_of_lt_one (norm_nonneg r) hr).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro n; rw [norm_mul,norm_pow]; exact mul_le_of_le_one_left (by positivity) (c_norm n)

lemma bin_nonneg (r : ℝ) (hr : 0 ≤ r) : 0 ≤ bin r := tsum_nonneg fun _ => mul_nonneg (c_nn _) (pow_nonneg hr _)

lemma bin_sq (r : ℝ) (hr : 0 ≤ r) (hr' : r < 1) : bin r ^ 2 = (1-r)⁻¹ := by
  have hs := bin_summable r (by rwa [Real.norm_of_nonneg hr])
  rw [sq, bin, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hs hs]
  calc
    _ = ∑' k : ℕ, r^k := tsum_congr fun k => by
      conv_rhs => rw [← one_mul (r^k), ← c_conv k, Finset.sum_mul]
      apply sum_congr rfl; intro p hp
      rw [← mem_antidiagonal.mp hp, pow_add]; ring
    _ = _ := tsum_geometric_of_lt_one hr hr'
end YM.CF.SignScalar

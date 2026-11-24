import YM.CF.Operator.Basic

/-!
# Negative-mass Hermitian Wilson matrix

We will represent the lattice translations with matter parallel transport (all colors
and copies jointly). The estimate uses their commutator in L² operator norm. In particular
regularity of the gauge configuration is only required on plaquettes (in the representation
used), not closeness of the configuration to a flat connection. Nothing here is an inverse
estimate for the massless Weyl propagator. Cf. `the construction notes` (sign and
normalization conventions); here we use the factors `1-T` to estimate the anticommutators.
-/

set_option autoImplicit false
noncomputable section
namespace YM.CF
open scoped MatrixOrder Matrix.Norms.L2Operator BigOperators
attribute [local instance] opCStarAlgebra
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Translations include the spin structure signs, are unitary and commute with spin. -/
structure WilsonFrame (n : Type*) [Fintype n] [DecidableEq n] where
  T : Fin 4 → Op n
  gamma : Fin 4 → Op n
  chir : Op n
  shiftU i : T i ∈ unitary (Op n)
  gammaSA i : IsSelfAdjoint (gamma i)
  gammaSq i : gamma i * gamma i = 1
  cliff i j (h : i ≠ j) : gamma i * gamma j = -(gamma j * gamma i)
  spins i j : Commute (gamma i) (T j)
  chirSA : IsSelfAdjoint chir
  chirSq : chir * chir = 1
  graded i : chir * gamma i = -(gamma i * chir)
  signs i : Commute chir (T i)

namespace WilsonFrame
variable (W : WilsonFrame n)

def lap (i : Fin 4) : Op n := 1 - (1/2 : ℝ) • (W.T i + star (W.T i))
def diff (i : Fin 4) : Op n := (1/2 : ℝ) • (W.T i - star (W.T i))
def inc (i : Fin 4) := W.lap i + W.gamma i * W.diff i

/-- Negative-mass Wilson operator: on commuting scalar translations with phase eⁱᵖ
it has symbol b(p) + i ∑ sin(p_μ) γ_μ. -/
def H0 : Op n := -1 + ∑ i, W.inc i

/-- Hermitian matrix used for the chiral projection. -/
def H : Op n := W.chir * W.H0

lemma lap_factor (i) : W.lap i = (1/2 : ℝ) • (star (1-W.T i) * (1-W.T i)) := by
  have h₁ : star (W.T i) * W.T i = 1 := (W.shiftU i).1
  simp only [lap, star_sub, star_one, mul_sub, sub_mul, one_mul, h₁, mul_one]
  module
lemma lap_sa (i) : IsSelfAdjoint (W.lap i) := by
  rw [W.lap_factor]; exact (IsSelfAdjoint.all _).smul (.star_mul_self _)
lemma lap_nonneg (i) : 0 ≤ W.lap i := by
  rw [W.lap_factor]; exact smul_nonneg (by norm_num) (star_mul_self_nonneg _)
lemma diff_skew (i) : star (W.diff i) = - W.diff i := by
  unfold diff; rw [star_smul, star_trivial,star_sub,star_star, ← neg_sub,smul_neg]
lemma spin_star (i j) : Commute (W.gamma i) (star (W.T j)) := by
  have h := (W.spins i j).star_star; rwa [(W.gammaSA i).star_eq] at h
lemma spin_lap (i j) : Commute (W.gamma i) (W.lap j) :=
  (Commute.one_right _).sub_right (((W.spins i j).add_right (W.spin_star i j)).smul_right _)
lemma spin_diff (i j) : Commute (W.gamma i) (W.diff j) :=
  ((W.spins i j).sub_right (W.spin_star i j)).smul_right _
lemma chir_star (j) : Commute W.chir (star (W.T j)) := by
  have h := (W.signs j).star_star; rwa [W.chirSA.star_eq] at h
lemma chir_lap (j) : Commute W.chir (W.lap j) :=
  (Commute.one_right _).sub_right (((W.signs j).add_right (W.chir_star j)).smul_right _)
lemma chir_diff (j) : Commute W.chir (W.diff j) :=
  ((W.signs j).sub_right (W.chir_star j)).smul_right _
lemma star_inc (i) : star (W.inc i) = W.lap i - W.gamma i * W.diff i := by
  simp only [inc, star_add, (W.lap_sa i).star_eq, star_mul, (W.gammaSA i).star_eq, W.diff_skew,
    mul_neg, (W.spin_diff i i).eq, sub_eq_add_neg]
lemma star_inc_mul_chir (i) : star (W.inc i) * W.chir = W.chir * W.inc i := by
  rw [W.star_inc, inc, sub_mul, mul_add, (W.chir_lap i).eq,
    mul_assoc (W.gamma i), ← (W.chir_diff i).eq, ← mul_assoc W.chir, W.graded]
  simp only [neg_mul,mul_assoc, sub_eq_add_neg]
lemma star_H0 : star W.H0 * W.chir = W.chir * W.H0 := by
  simp only [H0, star_add, star_neg,star_one, add_mul, mul_add, Matrix.sum_mul,
    Matrix.mul_sum, mul_neg, neg_mul, mul_one,one_mul, star_sum, W.star_inc_mul_chir]
lemma selfadjoint : IsSelfAdjoint W.H := by
  rw [isSelfAdjoint_iff,H,star_mul,W.chirSA.star_eq,W.star_H0]
lemma H_square : W.H*W.H = star W.H0 * W.H0 := by
  conv_lhs => lhs; rw [← W.selfadjoint.star_eq]
  unfold H; rw [star_mul, W.chirSA.star_eq, mul_assoc, ← mul_assoc W.chir, W.chirSq, one_mul]

lemma lap_diff (i) : Commute (W.lap i) (W.diff i) := by
  have h : Commute (W.T i) (star (W.T i)) := ((W.shiftU i).2.trans (W.shiftU i).1.symm : W.T i * star (W.T i) = _)
  exact ((Commute.one_left _).sub_left
    (((Commute.refl _).add_left h.symm).smul_left _)).sub_right
    ((Commute.one_left _).sub_left ((h.add_left (Commute.refl _)).smul_left _)) |>.smul_right _
lemma lap_diff_sq (i) : W.lap i * W.lap i - W.diff i * W.diff i = W.lap i + W.lap i := by
  have ha : W.T i * star (W.T i) = 1 := (W.shiftU i).2
  have hb : star (W.T i) * W.T i = 1 := (W.shiftU i).1
  simp only [lap,diff, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, add_mul, mul_add,
    mul_sub, sub_mul, one_mul, mul_one, ha, hb]
  -- check simp order
  module
lemma self_inc (i) : star (W.inc i) * W.inc i = star (W.inc i) + W.inc i := by
  have h : Commute (W.lap i) (W.gamma i * W.diff i) :=
    (W.spin_lap i i).symm.mul_right (W.lap_diff i)
  have hc : W.gamma i * W.diff i * (W.gamma i * W.diff i) = W.diff i * W.diff i := by
    rw [← mul_assoc, mul_assoc (W.gamma i), ← (W.spin_diff i i).eq]
    rw [← mul_assoc, W.gammaSq, one_mul]
  rw [W.star_inc, inc, sub_mul,mul_add,mul_add,h.eq,hc]
  rw [show W.lap i * W.lap i = W.lap i + W.lap i + W.diff i * W.diff i from
    sub_eq_iff_eq_add.mp (W.lap_diff_sq i)]
  abel

variable [Nonempty n]
lemma gamma_norm (i) : ‖W.gamma i‖ = 1 := CStarRing.norm_of_mem_unitary (by
  constructor <;> rw [(W.gammaSA i).star_eq, W.gammaSq])
lemma chir_norm : ‖W.chir‖ = 1 := CStarRing.norm_of_mem_unitary (by
  constructor <;> rw [W.chirSA.star_eq,W.chirSq])
lemma shift_norm (i) : ‖W.T i‖ = 1 := CStarRing.norm_of_mem_unitary (W.shiftU i)

variable {i j : Fin 4} {A : Op n} {e : ℝ}
lemma half_step (e : ℝ) : ‖(1/2 : ℝ)‖ * (e+e) = e := by rw [Real.norm_of_nonneg (by norm_num)]; ring
lemma lap_switch (h : Switch (W.T i) A e) : Switch (W.lap i) A e := by
  have he := (Switch.fromCommute (Commute.one_left A)).sub_left
    ((h.add_left (h.star_left (W.shiftU _))).smul_left (1/2))
  rw [zero_add, half_step] at he; exact he
lemma diff_switch (h : Switch (W.T i) A e) : Switch (W.diff i) A e := by
  have he := (h.sub_left (h.star_left (W.shiftU _))).smul_left (1/2)
  rw [half_step] at he; exact he

lemma lap_pair_err (hw : Switch (W.T i) (W.T j) e) :
    let A := 1-W.T i
    ‖W.lap i * W.lap j + W.lap j * W.lap i - star A * W.lap j * A‖ ≤ e + e := by
  intro A
  let L := W.lap j
  let X := W.lap i * L - (1/2:ℝ) • (star A * L * A)
  have hlt : Switch (W.T i) L e := (W.lap_switch hw.symm).symm
  have hs : Switch A L e := by
    have he := (Switch.fromCommute (Commute.one_left L)).sub_left hlt
    rwa [zero_add] at he
  have hb : ‖A‖ ≤ 2 := (norm_sub_le (1 : Op n) (W.T i)).trans (by rw [norm_one,W.shift_norm]; norm_num)
  have hxb : ‖X‖ ≤ e := by
    rw [show X = (1/2:ℝ) • (star A * (A*L-L*A)) by
      dsimp only [X]
      rw [W.lap_factor i, Algebra.smul_mul_assoc, ← smul_sub]
      congr 1
      change star A * A * L - star A * L * A = _
      rw [mul_sub (star A) (A*L) (L*A), mul_assoc, mul_assoc]]
    calc
      _ ≤ ‖(1/2:ℝ)‖ * (2 * e) := by
        rw [norm_smul]
        refine mul_le_mul_of_nonneg_left ((norm_mul_le ..).trans ?_) (norm_nonneg _)
        rw [norm_star]
        exact mul_le_mul hb hs (norm_nonneg _) (by norm_num)
      _ = e := by rw [two_mul, half_step]
  have ha : IsSelfAdjoint (star A * L * A) := .of_nonneg
    (star_left_conjugate_nonneg (W.lap_nonneg _) _)
  change ‖W.lap i*L+L*W.lap i-star A*L*A‖ ≤ _
  rw [show W.lap i*L+L*W.lap i-star A*L*A = X+star X by
    rw [show star X = L*W.lap i - (1/2:ℝ) • (star A*L*A) by
      unfold X; rw [star_sub,star_mul, (show IsSelfAdjoint L from W.lap_sa j).star_eq,
        (W.lap_sa i).star_eq,star_smul,star_trivial,ha.star_eq]]
    dsimp only [X]; module]
  exact (norm_add_le ..).trans (add_le_add hxb (by rwa [norm_star]))

lemma cross_bound (hne : i ≠ j) (hw : Switch (W.T i) (W.T j) e) :
    -((5*e) • (1 : Op n)) ≤ star (W.inc i) * W.inc j + star (W.inc j) * W.inc i := by
  let A := 1-W.T i
  let B := star A * W.lap j * A
  have hB : 0 ≤ B := star_left_conjugate_nonneg (W.lap_nonneg _) _
  let Y := star (W.inc i) * W.inc j + star (W.inc j) * W.inc i
  have hy : IsSelfAdjoint (Y-B) := (show IsSelfAdjoint Y by
    rw [isSelfAdjoint_iff]; simp [Y, star_add, star_mul, add_comm]).sub (.of_nonneg hB)
  apply le_trans (b := Y-B) _ (sub_le_self _ hB)
  apply op_ge_neg_scalar hy
  let V := W.lap i * W.lap j + W.lap j * W.lap i - B
  let P := W.gamma j * (W.lap i * W.diff j - W.diff j * W.lap i)
  let Q := W.gamma i * (W.lap j * W.diff i - W.diff i * W.lap j)
  let R := W.gamma i * W.gamma j * (W.diff i * W.diff j - W.diff j * W.diff i)
  have ht (i j) : W.lap i * (W.gamma j * W.diff j) = W.gamma j * (W.lap i * W.diff j) := by
    rw [← mul_assoc, ← (W.spin_lap j i).eq, mul_assoc]
  have hd (i j) : W.gamma i * W.diff i * (W.gamma j * W.diff j) =
      W.gamma i * W.gamma j * (W.diff i * W.diff j) := by
    rw [← mul_assoc, mul_assoc (W.gamma i), ← (W.spin_diff j i).eq]; simp only [mul_assoc]
  rw [show Y-B = V+P+Q-R by
    simp only [Y,W.star_inc]
    simp only [V,P,Q,R,inc, mul_add,sub_mul, ht i j, ht j i, hd i j, hd j i,
      W.cliff j i hne.symm, neg_mul, mul_sub, mul_assoc]
    abel]
  have hg {a : Fin 4} {Z : Op n} {c : ℝ} (h : ‖Z‖ ≤ c) : ‖W.gamma a * Z‖ ≤ c :=
    (norm_mul_le ..).trans (by rw [W.gamma_norm, one_mul]; exact h)
  have hv : ‖V‖ ≤ e+e := W.lap_pair_err hw
  have hp : ‖P‖ ≤ e := hg (W.lap_switch (W.diff_switch hw.symm).symm)
  have hq : ‖Q‖ ≤ e := hg (W.lap_switch (W.diff_switch hw).symm)
  have hr : ‖R‖ ≤ e := by rw [show R = W.gamma i * (W.gamma j * _) from mul_assoc ..]; exact hg (hg (W.diff_switch (W.diff_switch hw.symm).symm))
  calc
    _ ≤ e+e+e+e+e := (norm_sub_le ..).trans (add_le_add
      ((norm_add_le ..).trans <| add_le_add ((norm_add_le ..).trans <| add_le_add hv hp) hq) hr)
    _ = _ := by ring

/-- Volume-independent lower bound in p.s.d. order. -/
theorem gap (hw : ∀ i j, i < j → Switch (W.T i) (W.T j) e) :
    (1-30*e) • (1 : Op n) ≤ W.H^2 := by
  let X := fun i j => star (W.inc i) * W.inc j + star (W.inc j) * W.inc i
  have he (i j) (h : i < j) : -((5*e) • (1 : Op n)) ≤ X i j :=
    W.cross_bound h.ne (hw i j h)
  rw [show W.H^2 = 1 + (X 0 1+X 0 2+X 0 3+X 1 2+X 1 3+X 2 3) by
    rw [sq, W.H_square]
    simp only [H0, Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
      star_add,star_neg,star_one, add_mul,mul_add,mul_one,one_mul,neg_mul,mul_neg,
      W.self_inc, X, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, show ((2:Fin 3).succ) = 3 by decide]
    abel]
  have hh := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (he 0 1 (by decide))
    (he 0 2 (by decide))) (he 0 3 (by decide))) (he 1 2 (by decide))) (he 1 3 (by decide))) (he 2 3 (by decide))
  calc
    _ = (1 : Op n) + _ := ?_
    _ ≤ _ := add_le_add le_rfl hh
  module

theorem bounded : ‖W.H‖ ≤ 13 := by
  have hl (i) : ‖W.lap i‖ ≤ 2 := (norm_sub_le ..).trans (by
    rw [norm_one,norm_smul,Real.norm_of_nonneg (by norm_num)]
    linarith [norm_add_le (W.T i) (star (W.T i)), W.shift_norm i, norm_star (W.T i)])
  have hd (i) : ‖W.diff i‖ ≤ 1 := by
    unfold diff; rw [norm_smul,Real.norm_of_nonneg (by norm_num)]
    linarith [norm_sub_le (W.T i) (star (W.T i)), W.shift_norm i, norm_star (W.T i)]
  have ht (i) : ‖W.inc i‖ ≤ 2+1 := (norm_add_le ..).trans (add_le_add (hl i)
    ((norm_mul_le ..).trans <| by rw [W.gamma_norm,one_mul]; exact hd i))
  unfold H
  calc
    _ ≤ ‖W.chir‖ * ‖W.H0‖ := norm_mul_le ..
    _ ≤ _ := by
      rw [W.chir_norm, one_mul]
      calc
        _ ≤ ‖(-1 : Op n)‖ + (∑ i : Fin 4, ((2+1) : ℝ)) := (norm_add_le ..).trans <| add_le_add le_rfl
          ((norm_sum_le ..).trans <| Finset.sum_le_sum fun i _ => ht i)
        _ = _ := by norm_num
end WilsonFrame
end YM.CF

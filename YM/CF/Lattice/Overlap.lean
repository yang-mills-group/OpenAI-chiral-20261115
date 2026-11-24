import YM.CF.Lattice.Frame

/-! Chiral kinetic map. The spinors used in the regulated path-integral will be
restricted to the positive band, tending to *negative* chirality near the origin of the free
symbol. Barred variables use the positive grading. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF
open scoped MatrixOrder Matrix.Norms.L2Operator Matrix Kronecker BigOperators
attribute [local instance] opCStarAlgebra
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
variable {X : Op n}
lemma Safe.polar_square (h : Safe X) : polarity X * polarity X=1 := by
  obtain ⟨U,d,rfl⟩ := spectral_exists X h.self
  rw [polarity_spectral U d h,spectral_mul, ← spectral_one U]; congr 1
  ext i; by_cases e:0< d i <;> simp [signRoles,e]
lemma Safe.polar_star (h : Safe X) : IsSelfAdjoint (polarity X) := by
  obtain ⟨U,d,rfl⟩ := spectral_exists X h.self; rw [polarity_spectral U d h]; exact spectral_adjoint ..
lemma Safe.polar_proj (h : Safe X) : polarity X * projector X=projector X := by
  rw [projector,Algebra.mul_smul_comm,mul_add,mul_one,h.polar_square,add_comm]
lemma Safe.eig_lower (h : Safe X) {U : UNI n} {d : n → ℝ} (hx : X=spectral U d) (i : n) : 1/2 ≤ d i^2 := by
  have he := h.margin
  rw [hx,spectral_pow, ← spectral_one U, spectral_smul,spectral_le] at he
  simpa using he i
lemma polarity_scalar (h : Safe X) (r : ℝ) (hr : 0 ≤ r) (hx : X*X=(r^2) • (1 : Op n)) :
    polarity X = r⁻¹ • X := by
  obtain ⟨U,d,rfl⟩ := spectral_exists X h.self
  rw [polarity_spectral U d h,spectral_smul]
  rw [spectral_mul,← spectral_one U,spectral_smul] at hx
  have he := (spectral_le _ _ _).mp hx.le
  have hf := (spectral_le _ _ _).mp hx.ge
  apply congrArg (spectral U); funext i
  have hi : d i ^ 2 = r^2 := by apply le_antisymm <;> [simpa [sq] using he i; simpa [sq] using hf i]
  have hj := h.eig_lower rfl i
  have hz : r ≠ 0 := by intro h; rw [h] at hi; linarith
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hi) with hh|hh
  · simp [signRoles,hh,lt_of_le_of_ne hr (Ne.symm hz),hz]
  simp [signRoles,hh, not_lt.mpr (neg_nonpos.mpr hr),hz]

namespace WilsonFrame
variable (W : WilsonFrame n)
/-- Positive *grading* projection. Not `projector H`. -/
def plus := (1/2:ℝ) • ((1:Op n)+W.chir)
lemma plusStar : IsSelfAdjoint W.plus := (IsSelfAdjoint.all _).smul ((show IsSelfAdjoint (1:Op n) from .one _).add W.chirSA)
lemma plusChir : W.plus * W.chir = W.plus := by simp only [plus,Algebra.smul_mul_assoc,add_mul,W.chirSq,one_mul,add_comm W.chir]
lemma chirPlus : W.chir * W.plus = W.plus := by simp only [plus,Algebra.mul_smul_comm,mul_add,W.chirSq,mul_one,add_comm W.chir]
lemma plusSq : W.plus*W.plus=W.plus := by
  nth_rw 2 [plus]
  rw [Algebra.mul_smul_comm,mul_add,mul_one,W.plusChir]; module

def overlap := (1/2:ℝ) • ((1:Op n)+W.chir * polarity W.H)
/-- This proves the equality on the restricted columns, including at Dirac
zeros or exceptional index. No inverse of `plus * P`. -/
lemma overlap_action (h : Safe W.H) : W.overlap * projector W.H = W.plus * projector W.H := by
  rw [plus,overlap,Algebra.smul_mul_assoc,Algebra.smul_mul_assoc,add_mul,add_mul,mul_assoc,h.polar_proj]
lemma gw (h : Safe W.H) :
    W.chir*W.overlap+W.overlap*W.chir = (W.overlap*W.chir*W.overlap)+(W.overlap*W.chir*W.overlap) := by
  unfold overlap
  simp only [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,add_mul,mul_add,
    one_mul,mul_one]
  simp only [mul_assoc, ← mul_assoc W.chir W.chir,W.chirSq,one_mul,mul_one,h.polar_square]
  module
end WilsonFrame
end YM.CF

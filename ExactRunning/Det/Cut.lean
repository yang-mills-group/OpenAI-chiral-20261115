import Mathlib.LinearAlgebra.Matrix.SchurComplement
import ExactRunning.Calc.Touch

/-!
# Restriction to an orthogonal cut

Compress before taking determinants; pass the excluded subspace through
unchanged to work with ordinary real determinants. Use `Real.log`
(`Real.log_abs`; log of absolute value on nonzero reals).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Matrix Filter
open scoped Topology ContDiff

namespace ExactRunning

variable {m n k j : Type} [Fintype m] [Fintype n] [Fintype k] [Fintype j]
  [DecidableEq m] [DecidableEq n] [DecidableEq k] [DecidableEq j]

/-- Projection on allowed modes (counting metrics). -/
@[ext] structure ModeCut (m : Type) [Fintype m] where
  e : Matrix m m ℝ
  sym : eᵀ = e
  idem : e * e = e

namespace ModeCut
variable (P : ModeCut m) (Q : ModeCut n) (R : ModeCut k) (S : ModeCut j)

def compMat (A : Matrix m m ℝ) : Matrix m m ℝ := P.e * A * P.e + (1 - P.e)
def cutdet (A : Matrix m m ℝ) := (P.compMat A).det
def cutlog (A : Matrix m m ℝ) := Real.log (P.cutdet A)

attribute [simp] sym idem

def direct : ModeCut (m ⊕ n) where
  e := fromBlocks P.e 0 0 Q.e
  sym := by rw [fromBlocks_transpose]; simp
  idem := by rw [fromBlocks_multiply]; simp

def total : ModeCut m := ⟨1, transpose_one, by simp⟩

@[simp] lemma direct_e : (P.direct Q).e = fromBlocks P.e 0 0 Q.e := rfl
@[simp] lemma total_e : (total : ModeCut m).e = 1 := rfl

@[simp] lemma total_comp (A : Matrix m m ℝ) : (total.compMat A) = A := by simp [compMat]
@[simp] lemma total_det (A : Matrix m m ℝ) : total.cutdet A = A.det := by simp [cutdet]

@[simp] lemma compMat_id : P.compMat 1 = 1 := by simp [compMat]
@[simp] lemma compMat_transpose (A : Matrix m m ℝ) :
    P.compMat Aᵀ = (P.compMat A)ᵀ := by simp [compMat, transpose_mul, Matrix.mul_assoc]
@[simp] lemma cutdet_id : P.cutdet 1 = 1 := by simp [cutdet]
@[simp] lemma cutdet_transpose (A : Matrix m m ℝ) : P.cutdet Aᵀ = P.cutdet A := by simp [cutdet]

lemma compMat_one_add (A : Matrix m m ℝ) : P.compMat (1 + A) = 1 + P.e * A * P.e := by
  simp [compMat,Matrix.mul_add, Matrix.add_mul]
  abel

lemma compMat_fromBlocks (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n m ℝ) (D : Matrix n n ℝ) :
    (P.direct Q).compMat (fromBlocks A B C D) =
    fromBlocks (P.compMat A) (P.e * B * Q.e) (Q.e * C * P.e) (Q.compMat D) := by
  unfold compMat
  rw [direct_e, fromBlocks_multiply, fromBlocks_multiply, ← fromBlocks_one]
  ext (a|a) (b|b) <;> simp [Matrix.one_apply]

@[simp] lemma cutdet_lower (A : Matrix m m ℝ) (C : Matrix n m ℝ) (D : Matrix n n ℝ) :
    (P.direct Q).cutdet (fromBlocks A 0 C D) = P.cutdet A * Q.cutdet D := by
  simp only [cutdet, compMat_fromBlocks, Matrix.mul_zero,Matrix.zero_mul,det_fromBlocks_zero₁₂]

@[simp] lemma cutdet_upper (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ) :
    (P.direct Q).cutdet (fromBlocks A B 0 D) = P.cutdet A * Q.cutdet D := by
  simp only [cutdet, compMat_fromBlocks, Matrix.mul_zero,Matrix.zero_mul,det_fromBlocks_zero₂₁]

@[simp] lemma elim : P.e * (1-P.e) = 0 := by simp [Matrix.mul_sub]
@[simp] lemma elim' : (1-P.e) * P.e = 0 := by simp [Matrix.sub_mul]
@[simp] lemma comp_square : (1-P.e)*(1-P.e) = 1-P.e := by rw [Matrix.mul_sub,elim',mul_one,sub_zero]

lemma compMat_mul_aux (A B : Matrix m m ℝ) :
    P.compMat A * P.compMat B =
    (P.e * A * P.e) * (P.e * B * P.e) + (1 - P.e) := by
  unfold compMat
  rw [Matrix.mul_add, Matrix.add_mul,Matrix.add_mul,comp_square,
      Matrix.mul_assoc _ P.e (1-P.e), ← Matrix.mul_assoc (1-P.e), ← Matrix.mul_assoc (1-P.e)]
  simp

lemma proj_mul_aux (A : Matrix m n ℝ) (B : Matrix n k ℝ) :
    P.e * (A * B) * R.e - (P.e * A * Q.e) * (Q.e * B * R.e) =
    (P.e * A * (1-Q.e)) * ((1-Q.e) * B * R.e) := by
  rw [Matrix.mul_assoc _ _ (_*_*_), Matrix.mul_assoc _ _ ((1-Q.e)*_*_),
      ← Matrix.mul_assoc Q.e, ← Matrix.mul_assoc (1-Q.e),
      ← Matrix.mul_assoc Q.e, ← Matrix.mul_assoc (1-Q.e), idem, comp_square]
  simp only [Matrix.mul_assoc, Matrix.sub_mul,Matrix.mul_sub, Matrix.one_mul]

lemma compMat_mul_left (A B : Matrix m m ℝ) (ha : P.e * A = A * P.e) :
    P.compMat A * P.compMat B = P.compMat (A * B) := by
  have h := P.proj_mul_aux P P A B
  have : P.e * A * (1-P.e) = 0 := by rw [ha,Matrix.mul_assoc,P.elim,Matrix.mul_zero]
  rw [this,Matrix.zero_mul] at h
  rw [compMat_mul_aux, ← sub_eq_zero.mp h]; rfl
lemma compMat_mul_right (A B : Matrix m m ℝ) (hb : P.e * B = B * P.e) :
    P.compMat A * P.compMat B = P.compMat (A * B) := by
  have h := P.proj_mul_aux P P A B
  have : (1-P.e) * B * P.e = 0 := by rw [Matrix.mul_assoc, ← hb, ← Matrix.mul_assoc,P.elim',Matrix.zero_mul]
  rw [this,Matrix.mul_zero] at h
  rw [compMat_mul_aux, ← sub_eq_zero.mp h]; rfl

lemma cutdet_conj {T : Matrix m m ℝ} (ht : P.e * T = T * P.e) (hu : Tᵀ * T = 1)
    (A : Matrix m m ℝ) : P.cutdet (Tᵀ * A * T) = P.cutdet A := by
  have htt : P.e * Tᵀ = Tᵀ * P.e := by rw [← P.sym]; simpa only [transpose_mul] using congr_arg transpose ht.symm
  have hz : (P.compMat Tᵀ).det * (P.compMat T).det = 1 := by
    rw [← Matrix.det_mul,P.compMat_mul_right _ _ ht,hu,compMat_id,det_one]
  rw [cutdet,cutdet,← P.compMat_mul_right _ _ ht,← P.compMat_mul_left _ _ htt,det_mul,det_mul, mul_right_comm,hz,_root_.one_mul]
end ModeCut
end ExactRunning

import YM.Space.Index
import YM.Gauge.MatrixGroup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The ordinary rotations used by the obstruction
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.SatinRotation
open Lattice Filter Matrix
open scoped Topology Matrix.Norms.Frobenius

abbrev SO := ↥(Matrix.specialOrthogonalGroup Axis ℝ)

def roll (g : SO) (x : Axis → ℝ) := g.val *ᵥ x

def planeMatrix (φ : ℝ) : Matrix Axis Axis ℝ :=
  !![Real.cos φ, -Real.sin φ, 0, 0;
     Real.sin φ, Real.cos φ, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

lemma plane_orthogonal (φ : ℝ) : planeMatrix φ ∈ Matrix.specialOrthogonalGroup Axis ℝ := by
  rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff]
  have h := Real.sin_sq_add_cos_sq φ
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [planeMatrix, mul_apply, Axis, Fin.sum_univ_succ] <;> nlinarith
  unfold planeMatrix
  rw [det_succ_row_zero]
  simp [Fin.sum_univ_succ, det_fin_three]
  rw [show (Fin.succAbove (1 : Fin 4) 2) = 3 from rfl]
  simp only [cons_val]
  nlinarith

def planeRotation (φ : ℝ) : SO := ⟨planeMatrix φ, plane_orthogonal φ⟩

lemma plane_zero : planeRotation 0 = 1 := by
  apply Subtype.ext
  change planeMatrix 0 = 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [planeMatrix]

lemma plane_continuous : Continuous planeRotation := by
  apply Continuous.subtype_mk
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp [planeMatrix] <;> fun_prop

lemma roll_zero (φ : ℝ) (x : Axis → ℝ) :
    roll (planeRotation φ) x 0 = Real.cos φ * x 0 - Real.sin φ * x 1 := by
  simp [roll,planeRotation,planeMatrix,mulVec,dotProduct,Axis,Fin.sum_univ_succ,sub_eq_add_neg]
lemma roll_one (φ : ℝ) (x : Axis → ℝ) :
    roll (planeRotation φ) x 1 = Real.sin φ * x 0 + Real.cos φ * x 1 := by
  simp [roll,planeRotation,planeMatrix,mulVec,dotProduct,Axis,Fin.sum_univ_succ]
lemma roll_project (φ : ℝ) (x : Axis → ℝ) :
    Real.cos φ * roll (planeRotation φ) x 0 + Real.sin φ * roll (planeRotation φ) x 1 = x 0 := by
  rw [roll_zero,roll_one]
  calc
    _ = (Real.sin φ^2 + Real.cos φ^2) * x 0 := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq φ, one_mul]

lemma mixes {φ : ℝ} (p : 0 < |φ|) (q : |φ| < Real.pi / 2) : Real.sin φ ≠ 0 := by
  rcases lt_or_gt_of_ne (abs_pos.mp p) with h|h
  · have ht := Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr h)
      (show -φ < Real.pi from (neg_le_abs φ).trans_lt (q.trans (by linarith [Real.pi_pos])))
    rw [Real.sin_neg] at ht
    linarith
  exact (Real.sin_pos_of_pos_of_lt_pi h ((le_abs_self _).trans_lt (q.trans (by linarith [Real.pi_pos])))).ne'

lemma rotation_mix {φ : ℝ} (p : 0 < |φ|) (q : |φ| < Real.pi / 2) :
    (planeRotation φ).val 0 1 ≠ 0 ∧ (planeRotation φ).val 1 0 ≠ 0 := by
  simpa [planeRotation,planeMatrix] using mixes p q
lemma rotation_ne {φ : ℝ} (p : 0 < |φ|) (q : |φ| < Real.pi / 2) : planeRotation φ ≠ 1 := by
  intro he
  have ha := (rotation_mix p q).1
  rw [he] at ha
  apply ha
  change (1 : Matrix Axis Axis ℝ) 0 1 = 0
  simp [one_apply]

lemma rotation_limit : Tendsto planeRotation (𝓝 0) (𝓝 1) := plane_zero ▸ plane_continuous.continuousAt

lemma roll_homeo (g : SO) : ∃ f : (Axis → ℝ) ≃ₜ (Axis → ℝ), ⇑f = roll g := by
  obtain ⟨h,_⟩ := Matrix.mem_specialOrthogonalGroup_iff.mp g.property
  refine ⟨{ toFun := roll g
            invFun := fun x => g.val.transpose *ᵥ x
            left_inv := ?_
            right_inv := ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, rfl⟩
  · intro x
    change _ *ᵥ (_ *ᵥ x) = _
    rw [mulVec_mulVec, (Matrix.mem_orthogonalGroup_iff' ..).mp h, one_mulVec]
  · intro x
    change _ *ᵥ (_ *ᵥ x) = _
    rw [mulVec_mulVec, (Matrix.mem_orthogonalGroup_iff ..).mp h, one_mulVec]
  · show Continuous (roll g)
    unfold roll; fun_prop
  fun_prop

end YM.CF.SatinRotation

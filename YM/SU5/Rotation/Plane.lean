import YM.Space.Index
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Instances.Matrix

/-!
# Proper rotations, (0,1) plane

Here and in the obstruction theorem **0** is the chosen Euclidean time axis (as
on the elected panel and in the manuscripts). Not `YM.timeAxis` of older conventions.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SU5Rotation.Plane
open Real Matrix Set Filter
open scoped Topology Matrix

/-- Usual topology (entrywise), act on column vectors by left multiplication. -/
abbrev SO4 := ↥(Matrix.specialOrthogonalGroup Axis ℝ)

def R (θ : ℝ) : Matrix Axis Axis ℝ :=
  !![cos θ, -sin θ, 0, 0; sin θ, cos θ, 0, 0; 0,0,1,0; 0,0,0,1]

theorem orthog (θ : ℝ) : R θ ∈ Matrix.orthogonalGroup Axis ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [R, Matrix.mul_apply, Axis, Fin.sum_univ_succ] <;>
    nlinarith [Real.sin_sq_add_cos_sq θ]

theorem det_one (θ : ℝ) : (R θ).det=1 := by
  rw [Matrix.det_succ_row (R θ) 3]
  rw [Finset.sum_eq_single (3:Axis)]
  · rw [Matrix.det_fin_three]
    let c := cos θ
    let s := sin θ
    change (-1)^((3:ℕ)+3) * 1 *
      (c*c*1 - c*0*0 - -s*s*1 + -s*0*0 + 0*s*0 - 0*c*0) = 1
    dsimp only [c,s]; norm_num; nlinarith [Real.sin_sq_add_cos_sq θ]
  · intro j _ hj
    have he : R θ 3 j=0 := by fin_cases j <;> first | rfl | exact (hj rfl).elim
    rw [he]; ring
  simp

def rotate (θ : ℝ) : SO4 :=
  ⟨R θ,Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨orthog θ,det_one θ⟩⟩

theorem rotate_zero : rotate 0 = 1 := by
  apply Subtype.ext; change R 0=1
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [R,Axis,Matrix.one_apply]

theorem continuous_rotate : Continuous rotate := by
  apply Continuous.subtype_mk
  apply continuous_matrix; intro i j; fin_cases i <;> fin_cases j <;> simp [R] <;> fun_prop

/-- Approaching the identity even as proper rotation matrices. -/
theorem lim_rotate : Tendsto rotate (𝓝[≠] 0) (𝓝 1) := by
  rw [←rotate_zero]; exact continuous_rotate.continuousWithinAt

theorem eventually_angles : ∀ᶠ θ : ℝ in 𝓝[≠] 0, θ ≠ 0 ∧ |θ| < Real.pi / 2 := by
  have h : ∀ᶠ θ : ℝ in 𝓝 0, |θ| < Real.pi/2 :=
    continuous_abs.continuousAt.eventually (gt_mem_nhds (by simp [Real.pi_pos]))
  exact (show ∀ᶠ θ : ℝ in 𝓝[≠] 0, θ ≠ 0 from self_mem_nhdsWithin).and (h.filter_mono nhdsWithin_le_nhds)

lemma sin_ne {θ : ℝ} (h : θ≠0) (e : |θ| < Real.pi/2) : sin θ ≠ 0 := by
  have hu := abs_lt.mp e
  obtain h|h := lt_or_gt_of_ne h
  · exact (sin_neg_of_neg_of_neg_pi_lt h (by linarith [hu.1, Real.pi_pos])).ne
  exact (sin_pos_of_pos_of_lt_pi h (by linarith [hu.2, Real.pi_pos])).ne'

theorem mixes {θ : ℝ} (h : θ ≠ 0) (e : |θ| < Real.pi/2) : (rotate θ).val 1 0 ≠ 0 :=
  sin_ne h e

def turn (θ : ℝ) (x : Four ℝ) : Four ℝ := (rotate θ).val *ᵥ x

@[simp] theorem turn_time (θ : ℝ) (x : Four ℝ) : turn θ x 0 = cos θ*x 0 - sin θ*x 1 := by
  simp [turn, rotate, R, Matrix.mulVec,dotProduct,Axis,Fin.sum_univ_succ, sub_eq_add_neg]

@[simp] theorem turn_space (θ : ℝ) (x : Four ℝ) : turn θ x 1 = sin θ*x 0 + cos θ*x 1 := by
  simp [turn, rotate, R, Matrix.mulVec,dotProduct,Axis,Fin.sum_univ_succ]

theorem turn_inverse (θ : ℝ) (x : Four ℝ) : turn (-θ) (turn θ x)= x := by
  change R (-θ) *ᵥ (R θ *ᵥ x) = _
  have he : R (-θ)=(R θ)ᵀ := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [R]
  rw [Matrix.mulVec_mulVec, he, (Matrix.mem_orthogonalGroup_iff' Axis ℝ).mp (orthog θ),
    Matrix.one_mulVec]

theorem turn_zero (x : Four ℝ) : turn 0 x=x := by
  rw [turn, rotate_zero]; exact Matrix.one_mulVec _

theorem continuous_turn : Continuous (Function.uncurry turn) := by
  apply continuous_pi; intro i
  change Continuous (fun x : ℝ × Four ℝ => ∑ j, (rotate x.1).val i j * x.2 j)
  apply continuous_finsetSum; intro j _
  exact (((continuous_subtype_val.comp continuous_rotate).comp continuous_fst).matrix_elem i j).mul
    ((continuous_apply j).comp continuous_snd)

theorem continuous_turn_single (θ : ℝ) : Continuous (turn θ) := by
  have h := continuous_turn.comp ((continuous_const (y:=θ)).prodMk (continuous_id (X:=Four ℝ)))
  simpa only [Function.comp_def, Function.uncurry_apply_pair, id_eq] using h

def turnHomeo (θ : ℝ) : Four ℝ ≃ₜ Four ℝ where
  toFun := turn θ
  invFun := turn (-θ)
  left_inv := turn_inverse θ
  right_inv x := by simpa only [neg_neg] using turn_inverse (-θ) x
  continuous_toFun := continuous_turn_single _
  continuous_invFun := continuous_turn_single _

lemma cos_pos_at {θ : ℝ} (e : |θ| < Real.pi/2) : 0 < cos θ := cos_pos_of_mem_Ioo (abs_lt.mp e)

theorem more_width {θ : ℝ} (h : θ≠0) (e : |θ| < Real.pi/2) : 1 < cos θ + |sin θ| := by
  have hs := abs_pos.mpr (sin_ne h e)
  have hc := cos_pos_at e
  nlinarith [Real.sin_sq_add_cos_sq θ, sq_abs (sin θ), mul_pos hs hc]

/-- In the direction of the rotated time axis. -/
theorem proj_turn (θ : ℝ) (x : Four ℝ) :
    cos θ*turn θ x 0 + sin θ*turn θ x 1 = x 0 := by
  have he := congrFun (turn_inverse θ x) 0
  simpa only [turn_time (-θ),cos_neg,sin_neg,neg_mul,sub_neg_eq_add] using he
end YM.SU5Rotation.Plane
#print axioms YM.SU5Rotation.Plane.rotate
#print axioms YM.SU5Rotation.Plane.lim_rotate
#print axioms YM.SU5Rotation.Plane.proj_turn
#print axioms YM.SU5Rotation.Plane.more_width

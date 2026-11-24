import YM.CF.Matter.Rep
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! Simple mass and conjugate-pair exclusion in the **labels**. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.SU
open scoped Matrix Matrix.Norms.L2Operator Topology Kronecker BigOperators
attribute [local instance] opCStarAlgebra
open Matrix

def z : ℂ := Complex.exp (2 * Real.pi * Complex.I / (↑(5:ℕ):ℂ))
lemma z_prim : IsPrimitiveRoot z 5 := Complex.isPrimitiveRoot_exp _ (by decide)
lemma z_n : ‖z‖ = 1 := by
  apply pow_left_inj₀ (norm_nonneg z) zero_le_one (show 5≠0 by decide) |>.mp
  rw [← norm_pow,z_prim.pow_eq_one]; simp
lemma z_uu : z*star z=1 := by
  rw [Complex.star_def, Complex.mul_conj,Complex.normSq_eq_norm_sq,z_n]; norm_num
lemma z_star : star z = z^4 := by
  apply mul_left_cancel₀ (show z ≠ 0 from z_prim.ne_zero (by decide))
  rw [z_uu]; exact (pow_succ' z 4 ▸ z_prim.pow_eq_one).symm

def central : E :=
  let A : Op F := diagonal fun _ => z
  let U : UNI F := ⟨A,by
    apply Matrix.mem_unitaryGroup_iff.mpr
    have h : star A = diagonal fun _ => star z := by
      ext x y; by_cases e:x=y <;> simp [A,e, Ne.symm]
    rw [h]; unfold A; rw [Matrix.diagonal_mul_diagonal]; simp only [z_uu]; simp⟩
  ⟨U,(show A.det=1 from by simp [A,F,z_prim.pow_eq_one])⟩

def charge (i : Slot) : ℕ := match i.2 with
| .inl _ => 2
| .inr _ => 4
lemma by_charge : (matter central).val = Matrix.diagonal (fun i => z^(charge i)) := by
  change (1:Op _) ⊗ₖ each (diagonal fun _ => z) = _
  have he : cc (diagonal fun _ : F => z) = diagonal (fun _ => z^4) := by
    ext i j; by_cases h:i=j <;> simp [h, show star z = z^4 from z_star] -- simp
  simp only [each,ExTwo.wedge_diag,he]
  ext ⟨b,i⟩ ⟨d,j⟩; by_cases e:b=d <;> cases i <;> cases j
    <;> simp [Matrix.diagonal_apply, Matrix.one_apply,Join.both,charge,F,Slot, Sheet,sq,e]
lemma charge_protect (i j : Slot) : ¬ (5 ∣ charge i+charge j) := by
  rcases i with ⟨b,i|i⟩ <;> rcases j with ⟨d,j|j⟩ <;> unfold charge <;> norm_num
/-- No invariant bilinear, even allowing all flavor mixing. -/
theorem no_mass (B : Op Slot) (h : ∀ U : E,
    (matter U).valᵀ*B*(matter U).val=B) : B=0 := by
  have he := h central; rw [by_charge, Matrix.diagonal_transpose] at he
  ext i j
  by_contra hh
  have hz : B i j ≠ 0 := hh
  have hj := Matrix.ext_iff.mpr he i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hj
  apply charge_protect i j (z_prim.dvd_of_pow_eq_one _ ?_)
  apply mul_right_cancel₀ hz
  rw [one_mul,pow_add]
  calc
    _ = _ := ?_
    _ = _ := hj
  ring
end YM.CF.SU

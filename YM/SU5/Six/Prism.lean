import YM.SU5.Six.ApplyPM
import YM.SU5.Six.PosMargin

/-! # Gram matrix of multiplier images -/
set_option autoImplicit false
noncomputable section

namespace YM.Spectral.PVM
open MeasureTheory Matrix
open scoped InnerProductSpace ComplexOrder MatrixOrder
variable {H : Hilbert} {X : Type*} [MeasurableSpace X]
         {f g : X → ℂ} {T U : H.Op} {P : PVM H X}
         {ι : Type*} (v : ι → H)

/-- Matrix entry `Z,Z' = ∫ f dν_{v Z,v Z'}` -/
def bill (P : PVM H X) (v : ι → H) (f : X → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => P.pairIntegral f (v i) (v j)

lemma Represents.gram (h : P.Represents f T) :
    Matrix.gram ℂ (fun i => T (v i)) = P.bill v (fun p => ↑(‖f p‖^2)) := by
  ext i j
  change inner ℂ _ _ = P.pairIntegral ..
  rw [← ContinuousLinearMap.adjoint_inner_right]
  exact h.square.on_pair _ _
lemma bill_ind (A : Set X) (hA : MeasurableSet A) :
    P.bill v (A.indicator fun _ => 1) = Matrix.gram ℂ (fun i => P.region A (v i)) := by
  have h := (P.represents_indicator _ hA).gram v
  let I := A.indicator fun _ => (1:ℂ)
  have he : (fun p => (↑(‖I p‖^2) : ℂ)) = I := by ext p; by_cases hp:p∈A <;> simp [I,hp]
  exact (congrArg (P.bill v) he.symm).trans h.symm

variable [Fintype ι]
lemma Represents.gram_le (h : P.Represents f T) (k : P.Represents g U)
    (hle : ∀ x, ∀ᵐ p ∂P.diagonal x, ‖f p‖ ≤ ‖g p‖) :
    Matrix.gram ℂ (fun i => T (v i)) ≤ Matrix.gram ℂ (fun i => U (v i)) := by
  refine YM.Six.gram_mono _ _ fun c => ?_
  let x := ∑ i, c i • v i
  suffices hv : ‖T x‖^2 ≤ ‖U x‖^2 by
    simpa only [x, map_sum, map_smul] using hv
  have hv := h.square.mono k.square x (show (fun p => (↑(‖f p‖^2):ℂ)) ≤ᵐ[P.diagonal x]
      (fun p => (↑(‖g p‖^2):ℂ)) by
    filter_upwards [hle x] with p hp
    exact_mod_cast pow_le_pow_left₀ (norm_nonneg _) hp 2)
  change inner ℂ x (T.adjoint (T x)) ≤ inner ℂ x (U.adjoint (U x)) at hv
  rw [ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K] at hv
  exact_mod_cast hv

lemma gram_projection_le (A : Set X) (hA : MeasurableSet A) :
    Matrix.gram ℂ (fun i => P.region A (v i)) ≤ Matrix.gram ℂ v := by
  refine (P.represents_indicator _ hA).gram_le v P.represents_one fun _ => ae_of_all _ fun p => ?_
  by_cases hp:p∈A <;> simp [hp]

end YM.Spectral.PVM

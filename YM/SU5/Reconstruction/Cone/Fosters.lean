import YM.SU5.Reconstruction.Cone.AxisCheck
/-!
# Transfer cone price to selected representations
Here basic order fact at play
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConePrice
open Function Set Filter MeasureTheory Measure InnerProductSpace Spectral OS Semigroup
open scoped BigOperators NNReal ENNReal Topology InnerProductSpace ComplexOrder
variable {H H' : Hilbert} {B : StarSubalgebra ℂ H.Op} [StarOrderedRing (↥B)] (T : B →⋆ₐ[ℂ] H'.Op)
lemma difference (W U : H.Op) : (∀ x:H, ‖W x‖≤‖U x‖) ↔ star W*W≤star U*U := by
  rw [ContinuousLinearMap.le_def]
  refine ⟨fun h=>⟨?_,?_⟩,fun h x=>?_⟩
  · -- IsSelfadj iff via def
    exact (((IsSelfAdjoint.star_mul_self U).sub (IsSelfAdjoint.star_mul_self W)).isSymmetric) -- name check
  · intro x
    change 0≤ RCLike.re (inner ℂ ((U.adjoint (U x))-(W.adjoint (W x))) x)
    rw [inner_sub_left,ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left,map_sub,inner_self_eq_norm_sq,inner_self_eq_norm_sq]; exact sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) (h x) _)
  have h := h.re_inner_nonneg_left x -- syntax?
  change 0≤ RCLike.re (inner ℂ ((U.adjoint (U x))-(W.adjoint (W x))) x) at h
  rw [inner_sub_left,ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left,map_sub,inner_self_eq_norm_sq,inner_self_eq_norm_sq] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (sub_nonneg.mp h)

lemma encourages {W U : B} (h : ∀ x:H, ‖W.val x‖ ≤ ‖U.val x‖) : ∀ y:H', ‖T W y‖ ≤ ‖T U y‖ := by
  apply (difference ..).mpr; have he:= (difference ..).1 h
  change star W * W ≤ star U * U at he -- subtype le issue
  rw [← map_star, ← map_star, ← map_mul, ← map_mul]; exact OrderHomClass.mono T he
end YM.ConePrice

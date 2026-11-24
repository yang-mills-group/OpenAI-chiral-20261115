import YM.SU5.Reconstruction.Cone.Fosters
/-!
# Root transfers soft price through allowance to ANY character.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConePrice
open Function Set Filter MeasureTheory Measure InnerProductSpace Spectral OS Semigroup
open scoped BigOperators NNReal ENNReal Topology InnerProductSpace ComplexOrder
variable {H H' : Hilbert} {B : StarSubalgebra ℂ H.Op} [StarOrderedRing (↥B)] (T : B →⋆ₐ[ℂ] H'.Op)
variable (δ:ℝ)
private lemma sa (x:ℝ): IsSelfAdjoint ((x:ℂ) • (1:H.Op)):= by change star _= _; simp
lemma updated (W U:H.Op) :
    (∀ x:H, ‖W x‖^2 ≤ ‖U x‖^2+δ*‖x‖^2) ↔ star W*W≤star U*U+(δ:ℂ) • (1:H.Op):= by
  rw [ContinuousLinearMap.le_def]
  refine ⟨fun h=>⟨((((IsSelfAdjoint.star_mul_self U).add (sa δ)).sub (IsSelfAdjoint.star_mul_self W)).isSymmetric),fun x=>?_⟩,fun h x=>?_⟩
  · change 0≤ RCLike.re (inner ℂ ((U.adjoint (U x)+(δ:ℂ) • x)-(W.adjoint (W x))) x)
    rw [inner_sub_left,inner_add_left,ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left,map_sub,map_add,inner_self_eq_norm_sq,inner_self_eq_norm_sq, inner_smul_left]; change 0≤ _+Complex.re _-_ ; simpa [Complex.mul_re,pow_two] using (sub_nonneg.mpr (h x)) -- tune
  have h:= h.re_inner_nonneg_left x
  change 0≤ RCLike.re (inner ℂ ((U.adjoint (U x)+(δ:ℂ) • x)-(W.adjoint (W x))) x) at h
  rw [inner_sub_left,inner_add_left,ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left,map_sub,map_add,inner_self_eq_norm_sq,inner_self_eq_norm_sq,inner_smul_left] at h; simp [Complex.mul_re,pow_two] at h; simpa only [pow_two] using h
lemma prices_any {W U : B} (h : ∀ x:H, ‖W.val x‖^2 ≤ ‖U.val x‖^2+δ*‖x‖^2) : ∀ y:H', ‖T W y‖^2 ≤ ‖T U y‖^2+δ*‖y‖^2 := by
  apply (updated ..).mpr; have he:= (updated ..).1 h
  change star W * W ≤ star U * U+ (δ:ℂ) • (1:B) at he
  have hs:= OrderHomClass.mono T he
  rw [map_mul,map_add,map_mul,map_star,map_star,map_smul,map_one] at hs; exact hs
end YM.ConePrice

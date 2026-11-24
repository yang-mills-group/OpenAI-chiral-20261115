-- standalone analysis lemmas for selection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.Normed.Module.Basic
/-!
# Loewner toolkit: uses the given operator order and the *subtype order*

No decision to change to a weaker subalgebra order at the boundary of the ground
space. We need positivity inherited by the cap algebra for compressions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SelectionAnalysis
open Function Filter Topology Set
open scoped Topology InnerProductSpace CStarAlgebra ComplexOrder NNReal ENNReal

variable {X Y : Type*}

section
variable [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X] (S : StarSubalgebra ℂ X)
  [IsClosed (S : Set X)]

/-- Use spectral permanence; we only need the subtype's C⋆ order. -/
theorem has_root (x : S) (h : 0 ≤ (x:X)) : ∃ y : S, x=star y*y := by
  letI : PartialOrder S := CStarAlgebra.spectralOrder _
  letI : StarOrderedRing S := CStarAlgebra.spectralOrderedRing _
  apply CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
  have hp : IsSelfAdjoint x := Subtype.ext (IsSelfAdjoint.of_nonneg h)
  apply (StarOrderedRing.nonneg_iff_spectrum_nonneg (R:=ℝ) x hp).2
  intro r hr
  have hm : algebraMap ℝ ℂ r ∈ spectrum ℂ x := spectrum.algebraMap_mem ℂ hr
  rw [StarSubalgebra.spectrum_eq S] at hm
  exact spectrum_nonneg_of_nonneg h ((spectrum.algebraMap_mem_iff ℂ).1 hm)

theorem subtypeOrder : StarOrderedRing S := by
  refine StarOrderedRing.of_nonneg_iff' (fun {x y} (h : x ≤ y) z => ?_) ?_
  · change z.val+x.val ≤ z.val+y.val
    exact add_le_add_right (show (x:X) ≤ (y:X) from h) z.val -- note mathlib add_le uses flipped
  intro x; refine ⟨fun h => has_root S x h, ?_⟩
  rintro ⟨y,rfl⟩; exact star_mul_self_nonneg (y:X)

end
section
open ContinuousLinearMap
variable [NormedAddCommGroup X] [InnerProductSpace ℂ X] (S : Submodule ℂ X) [S.HasOrthogonalProjection]

def squeeze : (X →L[ℂ] X) →L[ℂ] (S →L[ℂ] S) :=
  ((compL ℂ S X S) S.orthogonalProjectionOnto).comp ((compL ℂ S X X).flip S.subtypeL)
lemma squeeze_apply (x : X →L[ℂ] X) : squeeze S x = S.orthogonalProjectionOnto.comp (x.comp S.subtypeL) := rfl
lemma squeeze_one : squeeze S 1=1 := by
  ext1 x; exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x
lemma squeeze_nn {x : X →L[ℂ] X} (h : 0 ≤ x) : 0 ≤ squeeze S x :=
  (nonneg_iff_isPositive _).2 (((nonneg_iff_isPositive _).1 h).orthogonalProjectionOnto_comp S)

variable [CompleteSpace X] -- supplies extra HasOrthogonalProjection? Prop
lemma squeeze_star (x : X →L[ℂ] X) [CompleteSpace S] : squeeze S (star x) = star (squeeze S x) := by -- bracket order
  change squeeze S (adjoint x)=adjoint (squeeze S x)
  rw [squeeze_apply,squeeze_apply,adjoint_comp,adjoint_comp, Submodule.adjoint_subtypeL,
    Submodule.adjoint_orthogonalProjectionOnto,ContinuousLinearMap.comp_assoc]

end
end YM.SelectionAnalysis
#print axioms YM.SelectionAnalysis.subtypeOrder
#print axioms YM.SelectionAnalysis.squeeze_nn

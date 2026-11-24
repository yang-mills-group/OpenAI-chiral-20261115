import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
/-! * order on closed operator algebras. Use when projecting states. -/

noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Set CStarAlgebra
open scoped ComplexOrder Topology
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B] [PartialOrder A] [StarOrderedRing A]

lemma reflects_pos [PartialOrder B] [StarOrderedRing B] (f : B →⋆ₐ[ℂ] A) (hf : Injective f)
    (x : B) : 0 ≤ x ↔ 0 ≤ f x := by
  refine ⟨fun h => map_nonneg f h,fun h=>?_⟩
  have hx : IsSelfAdjoint (f x) := .of_nonneg h
  have ht : IsSelfAdjoint x := hf (by rw [map_star,hx.star_eq] : f (star x)=f x)
  rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R:=ℝ) (p:=IsSelfAdjoint) _ ht,
    ←ht.map_spectrum_real f hf]
  exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R:=ℝ) (p:=IsSelfAdjoint) _ hx).1 h
lemma reflects_order [PartialOrder B] [StarOrderedRing B] (f : B →⋆ₐ[ℂ] A) (hf : Injective f)
    (x y : B) : x ≤ y ↔ f x ≤ f y := by
  rw [←sub_nonneg,reflects_pos f hf,map_sub,sub_nonneg]

lemma closedStarOrdered (P : StarSubalgebra ℂ A) [IsClosed (P : Set A)] :
    StarOrderedRing P := by
  let orig := (inferInstance : PartialOrder P)
  suffices h : orig=CStarAlgebra.spectralOrder P from
    (show @StarOrderedRing _ _ orig _ from h.symm ▸ CStarAlgebra.spectralOrderedRing _)
  refine PartialOrder.ext (fun x y => ?_)
  change x.val ≤ y.val ↔ _
  letI inst : PartialOrder P := CStarAlgebra.spectralOrder P
  letI : StarOrderedRing P := CStarAlgebra.spectralOrderedRing P
  exact (reflects_order (P.subtype) Subtype.val_injective x y).symm
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice

import YM.SU5.Selected.Loewner
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Algebra.Group.Submonoid.Membership
/-!
# Operator assembly: topology toolkit
-/
set_option autoImplicit false
noncomputable section
namespace YM.SelectionAnalysis
open Function Filter Topology Set TopologicalSpace Metric
open scoped Topology InnerProductSpace NNReal ENNReal Pointwise

variable {X Y : Type*}

section algebra
variable [CStarAlgebra X] (S : Set X) (p : IsSeparable S)
include p
lemma unique_shelf : IsSeparable (Submonoid.closure S : Set X) := by
  let A := Nat.rec (motive := fun _ => Set X) ({1}:Set X) fun _ a => (fun x:X × X => x.1*x.2) '' (S ×ˢ a)
  have he (n:ℕ) : IsSeparable (A n) := by
    induction n with
    | zero => exact (finite_singleton _).isSeparable
    | succ n h => exact (p.prod h).image (continuous_fst.mul continuous_snd)
  apply (IsSeparable.iUnion he).mono
  intro x (h : x ∈ Submonoid.closure S)
  induction h using Submonoid.closure_induction_left with
  | one => exact mem_iUnion.mpr ⟨0,(show (1:X)∈{1} from rfl)⟩
  | mul_left x h y v k =>
    obtain ⟨n,p⟩ := mem_iUnion.mp k
    exact mem_iUnion.mpr ⟨n+1,show x*y ∈ (fun q:X×X => q.1*q.2) '' (S ×ˢ A n) from ⟨(x,y),⟨h,p⟩,rfl⟩⟩
lemma separable_cstar : SeparableSpace (StarAlgebra.adjoin ℂ S).topologicalClosure := by
  apply (IsSeparable.separableSpace (s:=closure (StarAlgebra.adjoin ℂ S:Set X)))
  have hs : IsSeparable (star S) := (p.image continuous_star).mono (by
    intro a h; exact ⟨star a,h,star_star a⟩)
  have hx := (unique_shelf (S∪star S) (p.union hs)).span (R:=ℂ) -- syntax
  apply IsSeparable.closure
  rw [← StarAlgebra.adjoin_eq_span] at hx
  exact hx
end algebra

-- This simple observation handles the equivariant subspaces. No extension of f needed.
lemma separable_small {Y Z : Type*} [PseudoMetricSpace Y] [TopologicalSpace Z] (p S : Set Y)
    (h : IsSeparable p) (f : S → Z) (hf : Continuous f) :
    IsSeparable (f '' {x:S|(x:Y)∈p}) := by
  let X := p ∩ S
  have hp : IsSeparable X := h.mono Set.inter_subset_left
  haveI : SeparableSpace X := hp.separableSpace
  let g : X → S := Set.inclusion Set.inter_subset_right
  apply (isSeparable_range (hf.comp (show Continuous g from continuous_inclusion _))).mono -- tune
  rintro z ⟨x,h,rfl⟩; exact ⟨⟨x.val,h,x.property⟩,rfl⟩
end YM.SelectionAnalysis
#print axioms YM.SelectionAnalysis.separable_cstar
#print axioms YM.SelectionAnalysis.separable_small

import SatinStress.U2.Coordinate
/-!
# Relative units (U3)

Real pointwise multiplication in Wick conserved-space coordinates. For finding the
unit we use a simplification of the interpolation argument in the MS. Doesn't
require identifying the equivalence relation on active coordinates. For each
active coordinate make an element 1 on it; the Boolean-union formula combines two
such assignments on *not necessarily disjoint* sets, not disturbing any previously
set to 1. And instead of using persistence of **simple real spectrum**, we give
a cyclic-vector argument for the units on the actual algebra with this weak limit.
Doesn't call for a multiplicative-algebra theorem *assuming* an associative or
commutative system on the actual operators.
-/

namespace SatinStress.U3
open Function U2 Coord Filter Set
open scoped Topology BigOperators

variable {K S I : Type*} {L : Filter I} [Field K] [AddCommGroup S] [Module ℝ S]

namespace Indicator

variable (W : Submodule K (I → K))
def lives (i : I) : Prop := ∃ x ∈ W, (x : I → K) i ≠ 0
lemma join (s : Finset I) (h : ∀ x ∈ W, ∀ y ∈ W, x*y ∈ W) :
    ∃ z ∈ W, ∀ i ∈ s, (lives W i → z i = 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0,W.zero_mem, fun _ he => (Finset.notMem_empty _ he).elim⟩
  | @insert i s hi hs =>
    obtain ⟨z,hz,hv⟩ := hs
    by_cases q : lives W i
    · obtain ⟨x,hx,hi⟩ := q
      let f := (x i)⁻¹ • x
      have he : f ∈ W := W.smul_mem _ hx
      have h1 : f i = 1 := by simp [f,hi]
      refine ⟨f+z-f*z, W.sub_mem (W.add_mem he hz) (h f he z hz), fun j hh hj => ?_⟩
      rcases Finset.mem_insert.mp hh with rfl|H
      · simp [h1]
      simp [hv j H hj]
    refine ⟨z,hz, fun j hh hj => ?_⟩; apply hv j _ hj
    exact (Finset.mem_insert.mp hh).resolve_left (fun t => q (t ▸ hj))

variable [Fintype I]
noncomputable def unit (W : Submodule K (I → K)) (i : I) : K := open scoped Classical in if lives W i then 1 else 0
omit [Fintype I] in
lemma unit_live {i} (e : lives W i) : unit W i = 1 := by unfold unit; rw [if_pos e]
omit [Fintype I] in
lemma unit_else {i} (e : ¬ lives W i) : unit W i = 0 := by unfold unit; rw [if_neg e]
lemma made (h : ∀ x ∈ W, ∀ y ∈ W, x*y ∈ W) : unit W ∈ W := by
  obtain ⟨z,hz,q⟩ := join W Finset.univ h
  convert hz using 1
  ext i
  by_cases H : lives W i
  · exact (unit_live W H).trans (q i (Finset.mem_univ _) H).symm
  rw [unit_else W H]; by_contra e; exact H ⟨z,hz,Ne.symm e⟩
omit [Fintype I] in
lemma unit_mul (x : W) : unit W * x.val=x.val := by
  ext i; by_cases h : x.val i=0
  · simp [h]
  simp [unit_live W (show lives W i from ⟨x.val,x.property,h⟩)]
omit [Fintype I] in
lemma live {x : I→K} (h : x ∈ W) (e : x ≠ 0) : ∃ i, lives W i := by
  obtain ⟨i,b⟩ := Function.ne_iff.mp e; exact ⟨i,x,h,b⟩
end Indicator

abbrev Left (S : Type*) [AddCommGroup S] [Module ℝ S] := S →ₗ[ℝ] (S→ₗ[ℝ] S)
namespace Left

variable (A : Left S) (x : S)
-- convenient forms outside assumptions
abbrev IsUnit := ∀ y, A x y = y
abbrev Cyclic := Surjective (A.flip x)

/-- Any element fixing this cyclic vector is **already** a left unit. -/
theorem already {x e : S} (h : Cyclic A x) (hp : A e x = x) (q : ∀ u v z, A u (A v z)=A v (A u z)) :
    IsUnit A e := by
  intro y; obtain ⟨z,rfl⟩ := h y; exact (q e z x).trans (congr_arg (A z) hp)

-- In perturbation, use the *right* map (not assumed = left!) of the given product.
-- at the limiting relative unit in commutative free algebra. Proves stability and
-- uniqueness of left units at all late i. And their entrywise convergence.
variable [FiniteDimensional ℝ S] {A} {x}
theorem survive {p : I → Left S} (h : Entries L (fun i => (p i).flip x) LinearMap.id)
    (q : ∀ i : I, ∀ u v w, p i u (p i v w)= p i v (p i u w)) :
    ∀ᶠ i in L, ∃! e, IsUnit (p i) e := by
  filter_upwards [eventually_inj h injective_id] with i hi
  have hu : Cyclic (p i) x := (LinearMap.injective_iff_surjective (f:=(p i).flip x)).mp hi
  obtain ⟨e,he⟩ := hu x
  exact ⟨e,already _ hu he (q i), fun b hb => hi ((hb x).trans he.symm)⟩

lemma tends {p : I → Left S} (h : Entries L (fun i => (p i).flip x) LinearMap.id)
    (f : I → S) (e : ∀ᶠ i in L, IsUnit (p i) (f i)) : Tends L f x := by
  apply recover h _ injective_id
  exact stationary.congr' (e.mono fun i hi => (hi x).symm)
end Left
end SatinStress.U3

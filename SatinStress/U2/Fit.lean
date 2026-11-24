import SatinStress.U2.Coordinate
/-!
# Rank comparison via tests

No generic-rank assumption on the rays, nor assuming the full derivative
exists on some next symbol space. In the last arrow of this chain the convergence
needed is only when testing the appropriate expressions in the separated-position
hierarchy. The following are the coordinate-free versions of the needed fitting
steps (including that it suffices to test the *free* rank on all or any separating
subset of those prices). We can ask for convergence for ℝ-valued probes; using real
and imaginary parts of a complex test is fine here.
-/
namespace SatinStress.U2.Coord

open Filter Function
open scoped Topology
variable {T U V V' Z I J : Type*} [AddCommGroup T] [Module ℝ T]
  [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup V'] [Module ℝ V'] [AddCommGroup Z] [Module ℝ Z]

variable {L : Filter I}
open Module (finrank)

/-- Even with i-dependent test choices on these spaces.
Their fixed limits must detect all of T. -/
theorem fitted [FiniteDimensional ℝ T] {x : I → T} {y : T}
    {f : I → J → T →ₗ[ℝ] ℝ} {g : J → T →ₗ[ℝ] ℝ}
    (h : ∀ j v, Tendsto (fun i => f i j v) L (𝓝 (g j v)))
    (hw : ∀ j, Tendsto (fun i => f i j (x i)) L (𝓝 (g j y)))
    (t : ∀ x : T, (∀ j, g j x = 0) → x=0) : Tends L x y := by
  obtain ⟨s,hs⟩ := YM.Work.A07.finite_rows g t
  exact recover (A:=fun i => LinearMap.pi fun j : s => f i j.val)
    (a:=LinearMap.pi fun j : s => g j.val)
    (fun x => iff_norm.mpr (tendsto_pi_nhds.mpr (fun j => h j.val x)))
    (iff_norm.mpr (tendsto_pi_nhds.mpr (fun j => hw j.val))) hs

section Semi
variable [FiniteDimensional ℝ T]
variable (a : T →ₗ[ℝ] V) (b : U →ₗ[ℝ] Z)

/-- Test convergence comparing (scaled) values in different ranges and on different
spaces. The varying linear frames `u` needn't be bijections for this bound. (Will apply
on isos, once bought by R part of the manuscript.) In particular X'/Z can be the product
spaces of *all kernel-test values*, not finite dimensional, and the prices can be on a
subset of those tests. Requiring that the free limiting prices separate `range a` rather
than the whole V is enough. -/
structure Confronts (L : Filter I) (u : I → T →ₗ[ℝ] U)
    (G : J → V →ₗ[ℝ] ℝ) (F : I → J → Z →ₗ[ℝ] ℝ) : Prop where
  -- permits rescaling on either argument: just use u or F with those scalar factors
  priced (j : J) (x : T) : Tendsto (fun i => F i j (b (u i x))) L (𝓝 (G j (a x)))
  detects (x : T) : (∀ j, G j (a x)=0) → a x=0

variable [FiniteDimensional ℝ U]
theorem Confronts.lesser {L : Filter I} [L.NeBot] {a : T →ₗ[ℝ] V} {b : U →ₗ[ℝ] Z}
    {u : I → T →ₗ[ℝ] U} {G : J → V →ₗ[ℝ] ℝ} {F : I → J → Z →ₗ[ℝ] ℝ}
    (t : Confronts a b L u G F) : finrank ℝ a.range ≤ finrank ℝ b.range := by
  -- lift range in free domain only
  obtain ⟨l,hl⟩ := a.rangeRestrict.exists_rightInverse_of_surjective a.range_rangeRestrict
  have he (x : a.range) : a (l x) = x.val := congr_arg Subtype.val (LinearMap.congr_fun hl x)
  obtain ⟨s,hs⟩ := YM.Work.A07.finite_rows (fun i : J => (G i).domRestrict a.range) (by
    intro x h; apply Subtype.ext; change x.val = 0
    rw [← he]; apply t.detects; intro p; rw [he]; exact h p)
  let f (i) := LinearMap.pi fun j : s => (F i j.val) ∘ₗ (b ∘ₗ (u i ∘ₗ l))
  have h : ∀ x j, Tendsto (fun i => f i x j) L (𝓝 (G j.val x.val)) := fun x j =>
    (he x ▸ t.priced j.val (l x) : Tendsto (fun i => F i j.val (b (u i (l x)))) L (𝓝 (G j.val x.val)))
  obtain ⟨i,hi⟩ := (eventually_inj (fun x => iff_norm.mpr (tendsto_pi_nhds.mpr (h x)) :
     Entries L f (LinearMap.pi fun j : s => (G j.val).domRestrict a.range)) hs).exists
  refine LinearMap.finrank_le_finrank_of_injective (f:=b.rangeRestrict ∘ₗ (u i ∘ₗ l)) (fun x y e => ?_)
  exact hi (funext fun j => congr_arg (F i j.val) (congr_arg Subtype.val e))

/-- Specialized rank lower bound when prices converge as matrices (into a *fixed*,
finite-dimensional target). Here `A`,`B` are the actually used linear input and
output frames (can include ε). The obligation transposes only finitely many tests;
no shared topology assumptions on the *varying physical* Hil data. -/
theorem lesser_entry {L : Filter I} [L.NeBot] {a : T →ₗ[ℝ] V} {b : U →ₗ[ℝ] Z}
    {A : I → T →ₗ[ℝ] U} {B : I → Z →ₗ[ℝ] V} [FiniteDimensional ℝ V]
    (e : Entries L (fun i => B i ∘ₗ b ∘ₗ A i) a) : finrank ℝ a.range ≤ finrank ℝ b.range := by
  let R : Confronts a b L A (fun f : V→ₗ[ℝ] ℝ => f) (fun i f => f ∘ₗ B i) := by
    refine ⟨fun f x => e x f,fun x h => ?_⟩
    let Q := (Module.finBasis ℝ V).equivFun
    apply Q.injective
    rw [map_zero]; exact funext fun i => h ((LinearMap.proj i) ∘ₗ Q.toLinearMap)
  exact R.lesser
end Semi
end SatinStress.U2.Coord

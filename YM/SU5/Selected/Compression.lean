import YM.SU5.Selected.Freeze
import Mathlib.Topology.Algebra.StarSubalgebra
/-!
# Actual C*-algebra of all compressed words, including across the scales

Prove commutativity as an OPERATOR identity on the *entire* joint ground,
not just exchange in one matrix element. The proof uses four slots in an
experiment. Fill them with arbitrary beacons - the slot list is without
repetition; the resolution indices and inputs need not be. Cf. also
`YM/Ground/Permute.lean` on a (very) different system. Here no
rotations supplied by a continuum purchase.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 1050000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selected
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Set Vacancy
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E) (s : ℕ)
variable {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b) (Qt : Clipped Y H (i ∘ a) (k ∘ b))
variable (j : Axis) (strict : Bool) (C : Arena Y H Q.circuit j 0 strict)
local notation "A" => Ark.Ht Y H Q.circuit j 0 strict C
local notation "R" => Aurora Y H V Q j strict C
local notation "π" => (R).orthogonalProjectionOnto
local notation "ω" => floorV Y H Q.circuit j 0 strict C
local notation "Ω" => seat0 Y H V Q j strict C
local notation "𝒳" t:max => cap Y H V t Q Qt j strict C
local notation "ℬ" t:max => boxOp Y H V t Q Qt j strict C
local notation "𝔙" t:max => Tower.Field Y H t j 0 strict
local notation "ιₜ" t:max => actor Y H t Q.circuit j 0 strict C

/-- A slab Entry for every actor. -/
lemma artist_fits_slab (x : 𝔙 s) : ∃ w, 0 < w ∧ ∃ f : Entry Y H s j strict w, f.val = x := by
  obtain ⟨S,v,e⟩ := (show ∃ S : Finset Cover,
    InTest K true S false x.val ∧ Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ S from
    ((purpose_ok ..).1 x.property).1)
  rw [area0] at e
  obtain ⟨d,c⟩ := Tower.sizes S
  obtain ⟨k,h⟩ := c j
  let w := k.natAbs + d + (K).ℓ + 1
  refine ⟨w, by unfold w; omega, ⟨x,S,v,?_⟩, rfl⟩
  intro a m
  have h' := (h a m).2
  have hB : 1 ≤ ruler Λ.block := ruler_gene Λ.block
  exact ⟨e a m, le_trans (b := (w:ℤ)) (by unfold w; omega) (by
    exact le_mul_of_one_le_left (by positivity) hB)⟩

/-- Keep the actor as a test in any `strict` setting. -/
def actorLabel (x : 𝔙 s) : observable K strict :=
  ⟨x.val,(exam j _ K ((purpose_ok ..).1 x.property).1).1,
    ((purpose_ok ..).1 x.property).2⟩

lemma cap_of_entry {w : ℕ} (f : Entry Y H s j strict w) (p : 0 < w) :
    (𝒳 s) (actorLabel Y H s j strict f.val) =
      (π).comp (((ℬ s) w f p).comp (R).subtypeL) := by
  let F := actorLabel Y H s j strict f.val
  let X : Veranda Y H s j strict F :=
    ⟨0,w,p,f,(relocate_zero K j F.property.1).symm⟩
  exact onAny Y H V s Q Qt j strict C X

lemma cap_plant (x : 𝔙 s) :
    (𝒳 s) (actorLabel Y H s j strict x) Ω = π ((ιₜ s) x) := by
  obtain ⟨w,p,f,rfl⟩ := artist_fits_slab Y H s j strict x
  rw [cap_of_entry _ _ _ _ Q Qt j strict C f p]
  change π (((ℬ s) w f p) ω) = _
  rw [lays]

abbrev groundRoom : Hilbert := { space := Aurora Y H V Q j strict C }
local notation "ℛ" => groundRoom Y H V Q j strict C

/-- One-argument apparatus for the density proof. -/
def instrument (F : Beacon K strict) : (groundRoom Y H V Q j strict C).Op :=
  (𝒳 (F.1)) F.2
local notation "𝕏" => instrument Y H V Q Qt j strict C

include V in
lemma allActors : DenseRange (C.plant) := by
  apply (sounds Y H V Q.circuit j 0 strict C).mono
  intro x h; obtain ⟨i,h⟩ := Set.mem_iUnion.mp h
  obtain ⟨u,rfl⟩ := h
  exact ⟨⟨i,u⟩,rfl⟩

/-- Density of compressed *single* operators applied to Ω: no Pelham estimates on
varying stencils are needed as all fixed finite s are already present. -/
theorem compressed_dense : DenseRange (fun F : Beacon (tent Y H) strict =>
    instrument Y H V Q Qt j strict C F Ω) := by
  have h : Surjective π := fun p =>
    ⟨_, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self p⟩
  refine (h.denseRange.comp (allActors Y H V Q j strict C) ((π).continuous)).mono ?_
  rintro _ ⟨k,rfl⟩
  exact ⟨(k.1, actorLabel Y H k.1 j strict k.2), cap_plant Y H V k.1 Q Qt j strict C k.2⟩

lemma norm_one_vac : ‖Ω‖ = 1 := vane Y H V Q.circuit j 0 strict C

/-- Occurrence labels include their level. Dual label implements
actual (Banach algebra) star, not plain complex conjugation. -/
noncomputable def reflectOn (x : Beacon K strict) : Beacon K strict :=
  (x.1, dual Y H j strict x.2)
local notation "θ" => reflectOn Y H j strict
lemma mat_star (x : Beacon (tent Y H) strict) :
    (𝕏 (θ x)) = star (𝕏 x) := (mirror_cap Y H V x.1 Q Qt j strict C).symm

private lemma four_test (w x y z : Beacon K strict) :
    inner ℂ (Ω:ℛ) (𝕏 w (𝕏 x (𝕏 y (𝕏 z Ω)))) =
      inner ℂ Ω (𝕏 w (𝕏 y (𝕏 x (𝕏 z Ω)))) := by
  let f (i : Fin 4) := (![w,x,y,z] : Fin 4 → Beacon K strict) i -- homogeneous indexing
  exact any_order Y H V Q Qt j strict C f ([0,1,2,3]:List (Fin 4)) [0,2,1,3]
    (by decide) (.cons _ (.swap _ _ _))

/-- Not following from single-observable compression. -/
theorem mechanisms_commute (x y : Beacon (tent Y H) strict) :
    Commute (𝕏 x) (𝕏 y) := by
  let F := fun x : Beacon K strict => 𝕏 x Ω
  let a := 𝕏 x * 𝕏 y
  let b := 𝕏 y * 𝕏 x
  apply DFunLike.coe_injective
  show ⇑a = ⇑b
  apply (compressed_dense Y H V Q Qt j strict C).equalizer a.continuous b.continuous
  funext z
  apply (compressed_dense Y H V Q Qt j strict C).eq_of_inner_right ℂ
  intro w
  change inner ℂ (𝕏 w Ω) (𝕏 x (𝕏 y (𝕏 z Ω))) = inner ℂ (𝕏 w Ω) (𝕏 y (𝕏 x (𝕏 z Ω)))
  rw [←ContinuousLinearMap.adjoint_inner_right, ←ContinuousLinearMap.adjoint_inner_right]
  have h := four_test Y H V Q Qt j strict C (θ w) x y z
  rw [mat_star] at h
  exact h

def displayAlgebra : StarSubalgebra ℂ (groundRoom Y H V Q j strict C).Op :=
  (StarAlgebra.adjoin ℂ (Set.range (instrument Y H V Q Qt j strict C))).topologicalClosure
local notation "𝔄" => displayAlgebra Y H V Q Qt j strict C

instance displayClosed : IsClosed (𝔄 : Set (ℛ).Op) := isClosed_closure

/-- Use the actual algebra, not an abstract moment comparator. -/
instance displayCommCStar : CommCStarAlgebra (𝔄) := by
  let U := StarAlgebra.adjoin ℂ (Set.range 𝕏)
  haveI : IsMulCommutative U := StarAlgebra.isMulCommutative_adjoin ℂ (by
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩
    exact mechanisms_commute Y H V Q Qt j strict C x y |>.eq) (by
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩
    rw [← mat_star]
    exact mechanisms_commute Y H V Q Qt j strict C x (θ y) |>.eq)
  letI := U.commSemiringTopologicalClosure (fun x y => IsMulCommutative.is_comm.comm x y)
  exact { (StarSubalgebra.cstarAlgebra (𝔄)) with
    mul_comm := fun (x y : U.topologicalClosure) => mul_comm x y }

lemma cap_displayed (F : observable (tent Y H) strict) : (𝒳 s) F ∈ 𝔄 :=
  StarSubalgebra.le_topologicalClosure (StarAlgebra.adjoin ℂ (Set.range 𝕏))
    (StarAlgebra.subset_adjoin ℂ _ (show _ ∈ Set.range (𝕏) from ⟨(s,F),rfl⟩))

/-- Useful for computing on normalized coordinates. -/
def display (F : observable (tent Y H) strict) : 𝔄 :=
  ⟨(𝒳 s) F, cap_displayed Y H V s Q Qt j strict C F⟩
lemma mirror_display (F : observable (tent Y H) strict) :
    display Y H V s Q Qt j strict C (dual Y H j strict F) = star (display Y H V s Q Qt j strict C F) :=
  Subtype.ext (mat_star Y H V Q Qt j strict C (s,F))

theorem display_cyclic : DenseRange (fun x : 𝔄 => x.val Ω) :=
  (compressed_dense Y H V Q Qt j strict C).mono (by
    rintro _ ⟨k,rfl⟩
    exact ⟨display Y H V k.1 Q Qt j strict C k.2,rfl⟩)

theorem display_faithful : Injective (fun x : 𝔄 => x.val Ω) := by
  intro x y (h : x.val Ω = y.val Ω)
  apply Subtype.ext; apply DFunLike.coe_injective
  apply (display_cyclic Y H V Q Qt j strict C).equalizer x.val.continuous y.val.continuous
  funext z
  change (x*z).val Ω = (y*z).val Ω
  rw [mul_comm x z, mul_comm y z]
  exact congrArg z.val h

end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.mechanisms_commute
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.display_cyclic
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.display_faithful

import YM.SU5.Selected.Localization

/-!
# Birthplace with a real χ, all of its positive marked norms

Each selected functional is the reading by χ of the Joint ground operator on **THIS** E.
Showing uniqueness of vacuum of these states, at least at some (typical) value, needs further
work. Not interpreting the χ as other regulators.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (j : Axis) (r : Bool) (C : Arena Y H Q.circuit j 0 r)
local notation "R" => Aurora Y H V Q j r C
local notation "A" => Ark.Ht Y H Q.circuit j 0 r C
local notation "W" => floorV Y H Q.circuit j 0 r C
local notation "F₊" n:max => Tower.Field Y H n j 0 r
local notation "φ" n:max => actor Y H n Q.circuit j 0 r C
local notation "Ω" => seat0 Y H V Q j r C
local notation "π₀" => (R).orthogonalProjectionOnto
local notation "N" n:max => cap Y H V n Q Qc j r C
local notation "Test" => Vacancy.observable (tent Y H) r
local notation "Lab" => Beacon (tent Y H) r

open Localization
open scoped ContDiff
local notation "B" => groundAlgebra Y H V Q Qc j r C
local notation "Ch" => CapCharacter Y H V Q Qc j r C
local notation "M" s:max => liftCap Y H V Q Qc j r C s
local notation "f" s:max => (plants Y H V Q Qc j r C s)
local notation "L₀" s:max => prepare Y H V Q Qc j r C s
local notation "J₀" => (↑(R) →L[ℂ] (A))

-- Over actual R space.
abbrev basisRoom : Hilbert := { space := (R) }

include V Q Qc C
lemma range_mono : Monotone (fun t : ℕ => LinearMap.range (plants Y H V Q Qc j r C t)) := by
  rintro i k p _ ⟨v,rfl⟩; exact ⟨Raise Y H Q.circuit j 0 r i k p v, plant_high Y H V Q Qc j r C i k p v⟩

def pipeline : Submodule ℂ J₀ := ⨆ s : ℕ, LinearMap.range (f s)
local notation "P" => pipeline Y H V Q Qc j r C
lemma leg_available (x : (P)) (m : ℕ) : ∃ (t : ℕ) (y : F₊ t), m ≤ t ∧ x.val = (L₀ t) y := by
  have h := range_mono Y H V Q Qc j r C
  obtain ⟨i,p⟩ := (Submodule.mem_iSup_of_directed _ h.directed_le).1 x.property
  obtain ⟨v,t⟩ := h (le_max_left i m) p
  exact ⟨_,_,le_max_right i m,t.symm⟩ -- not unique! rename lemma

def asLeg (s : ℕ) : F₊ s →ₗ[ℂ] (P) := LinearMap.codRestrict (P) (f s) (fun x => le_iSup (fun s : ℕ => LinearMap.range (f s)) s (show _∈LinearMap.range (f s) from ⟨x,rfl⟩)) -- maybe parentheses
local notation "F₁" s:max => asLeg Y H V Q Qc j r C s
lemma common_leg (s t : ℕ) (h : s ≤ t) (x : F₊ s) : (F₁ t) (Raise Y H Q.circuit j 0 r s t h x)=(F₁ s) x :=
  Subtype.ext (plant_high Y H V Q Qc j r C s t h x)
lemma owns_each (x y : (P)) : x.val.adjoint.comp y.val ∈ (B) := by
  obtain ⟨i,z,_,p⟩ := leg_available Y H V Q Qc j r C x 0
  obtain ⟨t,w,u,v⟩ := leg_available Y H V Q Qc j r C y i
  rw [p,v,←plant_high Y H V Q Qc j r C i t u,compute]; exact ((M t) _).property

lemma schematic (χ : Ch) : Blueprint (basisRoom Y H V Q j r C) (A) (P) (B) χ.toAlgHom.toLinearMap :=
  { owns := owns_each Y H V Q Qc j r C, positive := char_pos Y H V Q Qc j r C χ }

-- dependent definitions sometimes drop `t` args in ports; ensure marked.
local notation "Z" χ:max => schematic Y H V Q Qc j r C χ
abbrev Birthplace (χ : Ch) := (Z χ).Room
lemma realizeRoom (χ : Ch) : Nonempty (Birthplace Y H V Q Qc j r C χ) := (Z χ).can_room

-- actual normalized Hilbert vectors
-- beware binder `(χ : Ch)` parsing
variable {χ : CapCharacter Y H V Q Qc j r C} (U : Birthplace Y H V Q Qc j r C χ)
def markedActor (s : ℕ) : F₊ s →ₗ[ℂ] U.H := ((Z χ).bloom U).comp (F₁ s)
local notation "η" s:max => markedActor Y H V Q Qc j r C U s
lemma markedBond (s : ℕ) (x y : F₊ s) : (Z χ).bond ((F₁ s) x) ((F₁ s) y) = (M s) (bornTest Y H j r s x y) := Subtype.ext (compute Y H V Q Qc j r C s x y)
lemma affirmation (s : ℕ) (x y : F₊ s) : inner ℂ ((η s) x) ((η s) y) = χ ((M s) (bornTest Y H j r s x y)) := by
  change inner ℂ ((Z χ).bloom U _) ((Z χ).bloom U _) = _; rw [(Z χ).seeded, markedBond]; rfl
lemma path (s t : ℕ) (h : s ≤ t) (x : F₊ s) : (η t) (Raise Y H Q.circuit j 0 r s t h x) = (η s) x := congrArg ((Z χ).bloom U) (common_leg Y H V Q Qc j r C s t h x)
lemma born_dense (t : ℕ) : Dense (⋃ (v : ℕ) (_ : t ≤ v), Set.range (η v)) := by
  refine ((Z χ).bloom_dense U).mono ?_
  rintro _ ⟨x,rfl⟩; obtain ⟨s,u,p,h⟩ := leg_available Y H V Q Qc j r C x t
  exact Set.mem_iUnion.mpr ⟨s,Set.mem_iUnion.mpr ⟨p,⟨u,congrArg ((Z χ).bloom U) (Subtype.ext h.symm)⟩⟩⟩

local notation "ζ" s:max => unity Y H j 0 r s
-- χ unit only for actual cap; important for reconstruction.
def vacuum : U.H := (η 0) (ζ 0)
local notation "λ₀" => vacuum Y H V Q Qc j r C U
lemma normal_base (s : ℕ) : λ₀ = (η s) (ζ s) := by
  have he : (F₁ s) (ζ s) = (F₁ 0) (ζ 0) := Subtype.ext ((prepare_unit Y H V Q Qc j r C s).trans (prepare_unit Y H V Q Qc j r C 0).symm)
  exact congrArg ((Z χ).bloom U) he.symm
lemma actual_expect (s : ℕ) (x : F₊ s) : inner ℂ λ₀ ((η s) x) = marked Y H V Q Qc j r C χ s (toTest Y H j r s x) := by
  have hc : bornTest Y H j r s (ζ s) x=toTest Y H j r s x := by
    apply Subtype.ext; change mirror K j 0 1 * _ = _; rw [mirror_unit,one_mul]
  exact (congrArg (fun z : U.H => inner ℂ z ((η s) x)) (normal_base Y H V Q Qc j r C U s)).trans
    ((affirmation Y H V Q Qc j r C U s _ _).trans (congrArg (fun z => χ ((M s) z)) hc))
lemma vacuum_norm : ‖λ₀‖=1 := by
  have hx : inner ℂ λ₀ λ₀=1:= (actual_expect Y H V Q Qc j r C U 0 (ζ 0)).trans
    ((congrArg χ (read_unit Y H V Q Qc j r C 0)).trans χ.map_one)
  suffices h : ‖λ₀‖^2= (1:ℝ) by nlinarith [norm_nonneg λ₀]
  exact (@inner_self_eq_norm_sq ℂ _ _ _ _ λ₀).symm.trans (congrArg Complex.re hx)
end YM.CF.Buffered.Afterglow.Tower.Selection

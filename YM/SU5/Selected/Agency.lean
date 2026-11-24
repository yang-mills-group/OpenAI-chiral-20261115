import YM.SU5.Selected.Room
import YM.SU5.Selected.TimeWidth
import YM.SU5.Selected.SpaceWidth
/-!
# Pruner acts by the same operators on the new phase Hilbert space

Apply `Blueprint` component to the actual Law (Born witness), and pay movement
physical clocks both before and after projection. Pre-axiomatization for relativity;
spectrum beyond time-positive or local algebras not yet. `Ring` here is a room of
op resources, not claiming it is the physical local algebra. Includes all available
physical slab operators as such. Can read their values under this projection and see
them skip combination exactly where declared in laws. Also supplies a useful unselected
leg reading identity so this extends a bit beyond character on the single-point test.
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

open Localization Pruner
local notation "B" => groundAlgebra Y H V Q Qc j r C
local notation "P" => pipeline Y H V Q Qc j r C
local notation "J" => (↑(R) →L[ℂ] (A))
local notation "L₀" s:max => prepare Y H V Q Qc j r C s
local notation "x₀" s:max => asLeg Y H V Q Qc j r C s
local notation "τ" s:max => tick Y H s j 0 r
local notation "ρ" s:max => ripple Y H V s Q.circuit j 0 r C
local notation "y₀" s:max => boxOp Y H V s Q Qc j r C
local notation "ε₀" s:max => (clockdrive Y H V Q.circuit j 0 r C).move s
abbrev pruner : StarSubalgebra ℂ (A).Op := preserves (X:=basisRoom Y H V Q j r C) (Y:=A) (P)
local notation "Β" => pruner Y H V Q Qc j r C
variable (s : ℕ)

include V Q Qc C
lemma timeAction (t m : ℕ) (p : s ≤ t) (x : F₊ t) : ((ρ s) m).comp ((L₀ t) x)= (L₀ t) ((τ t) (amount Λ s t m) x):=by
  have he := (clockdrive Y H V Q.circuit j 0 r C).refines s t m p
  rw [show (ρ s) m=(ρ t) (amount Λ s t m) from he]; exact from_time_μ ..
-- tick and all mesh are Pruners. no implicit shift by shrinking clock.
def timePruner (t : ℕ) : Β := by
  have h : (ρ s) t ∈ Β := by
    change Left (X:=basisRoom Y H V Q j r C) (Y:=A) P _ ∧ Left (X:=basisRoom Y H V Q j r C) (Y:=A) P _
    have H' : star ((ρ s) t)=(ρ s) t := current_adjoint ..
    rw [H',and_self]; intro x; obtain ⟨u,v,h,e⟩ := leg_available Y H V Q Qc j r C x s
    rw [e,timeAction Y H V Q Qc j r C s u t h]; exact ((x₀ u) _).property
  exact ⟨(ρ s) t,h⟩

lemma widthAction (t w : ℕ) (x : Entry Y H s j r w) (p : 0 < w) (q : s ≤ t) (y : F₊ t) :
    ((y₀ s) w x p).comp ((L₀ t) y) =
      (L₀ t) (slabT Y H t j r _ (furnished Y H s Q j r w x t q) y) := by
  rw [refined_box Y H V s Q Qc j r C w x p t q,prepare_box] -- metavariable p issue

def stretches (w : ℕ) (x : Entry Y H s j r w) (p : 0 < w) : Β := by
  have h (x : Entry Y H s j r w) : Left (X:=basisRoom Y H V Q j r C) (Y:=A) P ((y₀ s) w x p) := by
    intro h; obtain ⟨v,y,t,h'⟩ := leg_available Y H V Q Qc j r C h s
    rw [h',widthAction Y H V Q Qc j r C _ v w x p t]; exact ((x₀ v) _).property
  exact ⟨(y₀ s) w x p,h x, by
    change Left _ (ContinuousLinearMap.adjoint ((y₀ s) w x p)); rw [SlabMark.respects]; exact h _⟩

section space
variable (v : Trans j)
local notation "N₀" s:max => sailV Y H V s Q.circuit j 0 r v.val v.property C
lemma sails_adj (p : ℤ) : ((N₀ s) p).adjoint=(N₀ s) (-p) := by
  ext1 x; apply ext_inner_left ℂ; intro y; rw [ContinuousLinearMap.adjoint_inner_right]
  rw [←sail_meter Y H V Q j r C s v.val v.property (-p) ((N₀ s) p y) x, sail_unit Y H V Q j r C s v.val v.property]

lemma spaceAction (z : ℤ) (t : ℕ) (p : s ≤ t) (x : F₊ t) :
    ((N₀ s) z).comp ((L₀ t) x)=(L₀ t) (sail Y H t j 0 r v.val v.property (smill Λ s t z) x) := by
  rw [sailV_high Y H V s Q.circuit j 0 r v.val v.property C z t p]; exact from_space_μ ..

def spacePruner (z : ℤ) : Β := by
  have h (z : ℤ) : Left (X:=basisRoom Y H V Q j r C) (Y:=A) P ((N₀ s) z) := by
    intro x; obtain ⟨t,f,p,e⟩ := leg_available Y H V Q Qc j r C x s
    rw [e,spaceAction Y H V Q Qc j r C s v z t p]; exact ((x₀ t) _).property
  exact ⟨(N₀ s) z,h z,by
    change Left _ (ContinuousLinearMap.adjoint ((N₀ s) z)); rw [sails_adj Y H V Q Qc j r C s v]; exact h _⟩
end space

-- operator action from same pruner
variable {χ : CapCharacter Y H V Q Qc j r C} (U : Birthplace Y H V Q Qc j r C χ)
local notation "Z" => schematic Y H V Q Qc j r C χ
local notation "H₀" => basisRoom Y H V Q j r C
local notation "η" s:max => markedActor Y H V Q Qc j r C U s
abbrev leave : (Β) →⋆ₐ[ℂ] U.H.Op := Blueprint.plays Z U
local notation "F₀" => leave Y H V Q Qc j r C U

include U
lemma reserve_norm (p : Β) : ‖F₀ p‖ ≤ ‖p.val‖ := (Z).implement_size U p
lemma reserve_pos (u : Β) (p : 0 ≤ u.val) : 0 ≤ F₀ u := (Z).remains_pos U u p

lemma acts_on (p : Β) (t : ℕ) (x : F₊ s) (y : F₊ t) (h : (L₀ t) y=p.val.comp ((L₀ s) x)) : F₀ p ((η s) x) = (η t) y :=
  ((Z).implement_law U p ((x₀ s) x)).trans (congrArg ((Z).bloom U) (Subtype.ext h.symm))

-- Compare bonds for arbitrary operator words in this algebra. `plays` is an actual hom.
lemma original_measure (p : Β) (x y : P) : inner ℂ ((x.val) Ω) (p.val (y.val Ω)) =
    inner ℂ Ω (((Z).bond x (Pruner.applyM (X:=H₀) (Y:=A) P p y)).val Ω) := by
  change _=inner ℂ Ω (x.val.adjoint (p.val (y.val Ω))); rw [ContinuousLinearMap.adjoint_inner_right]
lemma after_action (p : Β) (x y : P) : inner ℂ ((Z).bloom U x) (F₀ p ((Z).bloom U y)) =
    χ ((Z).bond x (Pruner.applyM (X:=H₀) (Y:=A) P p y)) := by
  exact (congrArg (inner ℂ ((Z).bloom U x)) ((Z).implement_law U p y)).trans ((Z).seeded U x _)
end YM.CF.Buffered.Afterglow.Tower.Selection

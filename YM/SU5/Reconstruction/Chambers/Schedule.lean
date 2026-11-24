import YM.SU5.Selected.CompassGlass
/-!
# Chamber schedules, exact Euclidean interval budget & full plane playback

List order allows *independent* permutations for every axis. Recursion gaps can
be moved in spectator coordinates when the local footprint in their *own* axis
is separated too; continuity and operator insertions there. Eventually used for
multiple variables and analytic extension.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Chambers.Schedule
open Function Filter Set MeasureTheory Analysis SelectionAnalysis OS
open scoped Topology InnerProductSpace NNReal ENNReal Classical

variable {α : Type*} {Γ : AddSubgroup ℝ}

local notation "R" => Axis→ℝ
local notation "M" => Axis→Γ
-- cost also for unbounded Type labels; use only l-support. Affine anchors as in order likelihood.
structure Fixture (Γ : AddSubgroup ℝ) (α : Type*) where
  low : α → Axis → Γ
  width : α → Axis → Γ
  positive (i:α) (j:Axis) : 0 < ((width i j):ℝ)

variable (B : Fixture Γ α)
namespace Fixture
variable (j : Axis)
def beginAt (p : α → Axis → Γ) (i : α) : Axis → Γ := p i+Pi.single j (B.low i j)
def depart (p : α → Axis → Γ) (i : α) : Axis → Γ := B.beginAt j p i + Pi.single j (B.width i j)

def start (p : α→Axis→ℝ) (i:α) : Axis→ℝ := p i + Pi.single j ((B.low i j):ℝ)
def stop (p : α→Axis→ℝ) (i:α) : Axis→ℝ := B.start j p i + Pi.single j ((B.width i j):ℝ)

lemma start_cont (i : α) : Continuous (fun p : α → Axis → ℝ => B.start j p i) := (continuous_apply i).add continuous_const
lemma stop_cont (i : α) : Continuous (fun p : α → Axis → ℝ => B.stop j p i) := (B.start_cont j i).add continuous_const

def paste (b : Axis→Γ) : Axis→ℝ := fun i => (b i).val
def enter (p : α→Axis→Γ) : α→Axis→ℝ := fun i=> paste (p i)

lemma enters_dense (p : Dense (Γ:Set ℝ)) : DenseRange (enter (Γ:=Γ) (α:=α)) := by
  apply DenseRange.piMap (X:=fun _:α => (Axis→Γ))
  intro _; exact DenseRange.piMap (X:=fun i:Axis => Γ) (fun _=> p.denseRange_val)

@[simp] lemma paste_add (p q : Axis→Γ) : paste (p+q)=paste p+paste q := rfl
@[simp] lemma paste_sub (p q : Axis→Γ) : paste (p-q)=paste p-paste q := rfl
@[simp] lemma paste_single (p : Γ) : paste (Pi.single j p)=Pi.single j (p:ℝ) := by
  ext i; by_cases h:i=j<;>simp [paste,h]
@[simp] lemma paste_begin (p : α→Axis→Γ) (i:α) : paste (B.beginAt j p i)=B.start j (enter p) i := by
  rw [beginAt,paste_add,paste_single]; rfl
@[simp] lemma paste_depart (p : α→Axis→Γ) (i:α) : paste (B.depart j p i)= B.stop j (enter p) i := by rw [depart,paste_add,paste_single,paste_begin]; rfl

-- inequalities (can include equality but use strict for continuity purchases)
def permission (strict : Bool) (p : α→Axis→ℝ) : (Axis→ℝ) → List α → Prop
| _,[] => True
| q,i::l => (if strict then 0 < (B.start j p i - q) j else 0 ≤ (B.start j p i - q) j) ∧ permission strict p (B.stop j p i) l

lemma permission_step (strict : Bool) (p : α→Axis→ℝ) (i:α) (q : R) (l : List α) :
    B.permission j strict p q (i::l) = ((if strict then 0 < (B.start j p i - q) j else 0 ≤ (B.start j p i - q) j) ∧ B.permission j strict p (B.stop j p i) l) := rfl

lemma permission_ge (p : α→Axis→ℝ) (q : Axis→ℝ) (l : List α) : B.permission j true p q l → B.permission j false p q l := by
  induction l generalizing q with
  | nil => exact id
  | cons i l ih=> simp only [permission_step, Bool.false_eq_true, ↓reduceIte]; rintro ⟨b,h⟩; exact ⟨le_of_lt b,ih _ h⟩

lemma permission_open {X : Type*} [TopologicalSpace X] (q : X → Axis → ℝ) (t : Continuous q)
    (p : X → α→Axis→ℝ) (h : Continuous p) (l : List α) : IsOpen {x | B.permission j true (p x) (q x) l} := by
  induction l generalizing q with
  | nil => exact isOpen_univ
  | cons i l ih =>
    simp_rw [permission_step, if_true]
    exact (isOpen_lt continuous_const ((continuous_apply j).comp (((B.start_cont j i).comp h).sub t))).inter
      (ih (fun x=> B.stop j (p x) i) ((B.stop_cont j i).comp h))

variable (a : Axis→Axis→Γ) (o : Axis→List α)
def ready (a : Axis→Axis→Γ) (o : Axis→List α) : Set (α→Axis→ℝ) := {p | ∀ j : Axis, B.permission j true p (paste (a j)) (o j)}

lemma ready_open : IsOpen (B.ready a o) := by simp_rw [ready,setOf_forall]; exact isOpen_iInter_of_finite fun i => B.permission_open i _ continuous_const id continuous_id _
end Fixture
open Fixture

variable {H : Hilbert} {j : Axis}
-- Fold with gap motion before introducing an object. Type of spacetime arbitrary
-- (M,R,Can complexify) as long as subtraction. Result is CLM, obey regularity
-- via uniform norm bounds or via carriers below. Keep separate start and exit so
-- strict verification can vary each gap in spectator mesh (project sequentially).
namespace Compose
variable {F : Type*} [Sub F]
def roll (U : α → F → H.Op) (W : α → H.Op) (P Q : α → F) : F → List α → H.Op
| _,[] => ContinuousLinearMap.id ℂ _
| q,i::l => (U i (P i - q)).comp ((W i).comp (roll U W P Q (Q i) l))

lemma roll_step (U : α → F → H.Op) (W : α → H.Op) (P Q : α → F) (q : F) (i:α) (l:List α):
    roll U W P Q q (i::l)= (U i (P i-q)).comp ((W i).comp (roll U W P Q (Q i) l)) := rfl
end Compose
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Chambers.Schedule

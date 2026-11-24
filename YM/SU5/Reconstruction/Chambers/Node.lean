import YM.SU5.Reconstruction.Chambers.Retain
/-! # Interpretation with all spacetime coordinates extended via projections -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Chambers.Schedule
open Function Filter Set MeasureTheory SelectionAnalysis OS Analysis Metric Germ
open scoped Topology InnerProductSpace NNReal ENNReal Classical
variable {Γ : AddSubgroup ℝ} {j : Axis} {H : Hilbert}
open Fixture Compose
variable (U : OS.Semigroup H j)
def route (p : Axis→ℝ) : H.Op:= (U.E (p j).toNNReal).comp (U.U (diameter p))
lemma route_cost (p : Axis→ℝ) (x : H) : ‖route U p x‖ ≤ ‖x‖ :=
  calc ‖route U p x‖ ≤ ‖(U.E (p j).toNNReal)‖*‖(U.U (diameter p)) x‖ := (U.E _).le_opNorm _
       _ ≤ ‖x‖ := by rw [U.unitary]; exact mul_le_of_le_one_left (norm_nonneg _) (U.shrinks _)
lemma cont_route {A : Type*} [TopologicalSpace A] (p : A→Axis→ℝ) (x : A → H) (h : Continuous p) (a : Continuous x):
    Continuous fun i=> route U (p i) (x i) := by
  unfold route; simp_rw [ContinuousLinearMap.comp_apply]; refine actor_continuous _ 1 zero_lt_one ?_ ?_ _ ?_
  · intro z y; exact ((U.E _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (U.shrinks _) (norm_nonneg _))
  · intro z; exact (U.continuousE z).comp (continuous_real_toNNReal.comp ((continuous_apply j).comp h))
  refine actor_continuous _ 1 zero_lt_one ?_ ?_ _ a
  · intro z y; rw [U.unitary,one_mul]
  intro z; exact (U.continuousU z).comp (((OS.Semigroup.SEP j).continuous.comp (PiLp.continuous_toLp 2 _)).comp h)

variable {α : Type*} (V : Fixture Γ α)
def pointsOp (W : α→ H.Op) (p:α→Axis→ℝ) (q: Axis→ℝ) (t: List α) : H.Op:= roll (fun _ => route U) W (V.start j p) (V.stop j p) q t

lemma cont_points {A : Type*} [TopologicalSpace A] (W : α→ H.Op)
    (p : A→ α→Axis→ℝ) (q : A→Axis→ℝ)(t:List α) (x:A→H) (c: Continuous p) (d:Continuous q) (h:Continuous x) :
    Continuous fun i=> pointsOp U V W (p i) (q i) t (x i) := by
  induction t generalizing q with
  | nil => exact h
  | cons i t ih=>
    simp only [pointsOp,roll_step,ContinuousLinearMap.comp_apply]; refine cont_route _ _ _ ?_ ((W i).continuous.comp ?_)
    · exact ((V.start_cont j i).comp c).sub d
    exact ih (fun a=> V.stop j (p a) i) ((V.stop_cont j i).comp c)

-- from precision of the RAW input to projections. Use *separate* glass forecast in representation.
variable (X : Sunbelt j Γ H) (hX : X.heat=U.E) (d : Dense (Γ:Set ℝ))
variable (h : ∀ i,∀ z:Γ,∀ t:ℝ≥0, ((X.track.crew i).play z).comp (U.E t)=(U.E t).comp ((X.track.crew i).play z))
local notation "A" => X.track.Realm X.list
local notation "F" => (X.track.aviator X.list)
local notation "q₀" => (F).orthogonalProjectionOnto
local notation "W'" => glass X d U h

def corrected (W:H.Op) : (A).Op := (q₀).comp (W.comp (F).subtypeL)
include hX
lemma career (x : H) (W : H.Op) (p : Axis→Γ) (u : A)(b: x = u.val) :
    (X.plane p) (X.track.stackS X.list (W x))=
      (route W' (paste p) (corrected X W u):A).val := by
  let y:= corrected X W u
  have hx : X.track.stackS X.list (W x)=( (corrected X W u) : F).val := by rw [b,stack_projection]; rfl
  rw [hx]; change X.heat _ (X.track.raw X.list _ ((y:F).val))=( (W').E (paste p j).toNNReal ((W').U _ (corrected X W u)) : F ).val
  rw [glass_heat, hX, ← glass_move X d U h]; rfl -- tune order

lemma career_all (B : α→ H.Op) (p : α→Axis→Γ) (q : Axis→Γ) (t : List α) (x : H) (u : A)(b: x=u.val) :
    funded X (fun (_:α) => X.list) B V p q t x = (pointsOp W' V (fun i=> corrected X (B i)) (enter p) (paste q) t u : A).val := by
  induction t generalizing q with
  | nil=>exact b
  | cons i t ih=>
    simp only [pointsOp,funded,roll_step,ContinuousLinearMap.comp_apply]
    rw [← paste_begin, ← paste_depart, ← paste_sub]
    exact career U X hX d h _ (B i) _ _ (ih (V.depart j p i)) -- other gaz stop occurrences V.stop partially applied vs vars
omit hX

-- Glue at dense-grid on open real chambers; close behind changed permutation filters.
theorem close_on_open {D : Type*} [TopologicalSpace D] {E : Type*} [TopologicalSpace E] [T2Space E]
    {B : Set D} (hB : Dense B) {f g : D → E} (p : Continuous f) (q : Continuous g) {D' : Set D} (a : IsOpen D') (b : EqOn f g (D'∩B)) : EqOn f g D' :=
  (Set.EqOn.closure b p q).mono (hB.open_subset_closure_inter a)
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Chambers.Schedule

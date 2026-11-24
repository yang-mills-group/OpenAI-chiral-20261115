import YM.SU5.Relativistic.Blocks
/-!
# Cube translation test
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Set Filter MeasureTheory
open MeshClock Germ Vacancy _root_.YM.SelectionAnalysis
open scoped Topology Classical NNReal ENNReal
variable {M:Mesh}
structure Packet (M:Mesh) where
  size : ℕ
  base : Axis → Stamp M
  weight : (Axis→ℝ) → ℂ
  closed_weight : ContinuousOn weight (UBox Axis)
namespace Packet
variable (W: Packet M)
-- Apply to Unit cube offsets. Normalized volume on OBox.
def density (x:Axis→ℝ) :ℂ:= W.weight x
local notation "A"=>Axis
local notation "s"=>W.size
local notation "Q" n:max=> (Axis→ Fin (M.L^n))
def region (x:A→ℝ) : Axis→ℝ:=fun i=> ((W.base i: Stamp M):ℝ)+x i*(mill M W.size:ℝ)
theorem sweeps_cont : Continuous W.region := by unfold region; fun_prop
local notation "R" k:max x:max=> smallCorner (M.L^k) x
/-- Mesh-only samples. -/
def near (k:ℕ) (x:A→ Fin (M.L^k)) (i:Axis): Stamp M:= W.base i+notch M (W.size+k) (x i).val
def score (k:ℕ) (x:A→ Fin (M.L^k)): ℂ:= W.weight (smallCorner (M.L^k) x)
lemma lines_near (t:ℕ)(x:Q t) (i:Axis) (h:Precise (W.size+t) (W.base i)): Precise (W.size+t) (W.near t x i):=by
 unfold near; rw [← tags_on (s+t) h, ←notch_add]; exact ⟨_,rfl⟩
lemma points_near (k:ℕ)(x:Axis→ Fin (M.L^k)) (i:A): ((W.near k x i: Stamp M):ℝ)= W.region (smallCorner (M.L^k) x) i:=by
 unfold near region; rw [AddSubgroup.coe_add]; apply congrArg₂ (·+·) rfl; rw [mark_time]; unfold smallCorner whenly; push_cast
 have he: (M.L:ℝ)^k*(mill M (W.size+k):ℝ)=(mill M W.size:ℝ) := by
    have h:=mill_finer M W.size (W.size+k) (by omega); rw [show W.size+k-W.size=k by omega] at h; simpa using congrArg NNReal.toReal h
 have hv:0 < (M.L:ℝ):= by exact_mod_cast lt_of_lt_of_le (by decide) M.Llarge
 rw [← he]; field_simp -- maybe
lemma lives (k:ℕ)(x:Q k) : smallCorner (M.L^k) x ∈ UBox Axis:= halfBox ((nearBox_inside _ (avg_num M k) x) (corner_in_box _ (avg_num M k) x))
lemma span_score : ∃ C:ℝ,0≤C∧∀ t:ℕ,∀ x:Q t, ‖W.score t x‖≤C:=by
 obtain ⟨c,hc⟩:=(isCompact_Icc.image_of_continuousOn W.closed_weight.norm).bddAbove -- tune
 refine ⟨|c|,abs_nonneg _,fun t x=> (hc (mem_image_of_mem _ (lives (M:=M) t x))).trans (le_abs_self _)⟩
lemma eventually_grids : ∀ᶠ n in atTop, W.size≤n ∧ ∀ i:Axis,Precise n (W.base i) := (eventually_ge_atTop _).and (eventually_all.mpr fun i=> ReadPrecise _)
end Packet
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Packet.points_near

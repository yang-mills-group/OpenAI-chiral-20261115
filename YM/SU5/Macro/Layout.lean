import YM.SU5.Obstruction.Finite
import YM.SU5.Relativistic.Box
import YM.SU5.Selected.Cairn.Giant
import YM.SU5.Reconstruction.Cross.Boundaries
/-!
# Siam geometry

One square paid mask on top of the early (lower-time & lower-space)
leg. Footprints in level-zero matter units, hence handstamp needed for Keeps etc.
Prove the packaging both for `footprint` and `silhouette`.
-/
set_option autoImplicit false
set_option maxHeartbeats 440000
set_option maxRecDepth 4500
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selection.Home
open Function Filter NormedSpace Metric SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Tapestry Tapestry.Altitude
open Tower.PhaseChoice Tower.Selected Tower.Reconstruction
open CF.SatinRotation CF.Pannier.Chancel.Attic.Cairn Buffered.Reliance Buffered.Reliance.ShortWave
open OS.Semigroup MeshClock
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H

namespace Siam
section pane
variable (M:Giant)

def wall : Face ℤ := (M.anchorY-step 1-step 2,⟨(1,2),by decide⟩)
def early := M.ascY ∪ faceSites (wall M)
lemma four : faceSites (wall M) = {M.anchorY-step 1-step 2, M.anchorY-step 2,M.anchorY, M.anchorY-step 1} := by
  let x : Cover:=M.anchorY
  let α:= x-step 1-step 2
  have h1 : α+Lattice.step 1=x-step 2:=by unfold α; abel
  have h2 : x-step 2+step 2=x:=sub_add_cancel ..
  have h3 : α+Lattice.step 2=x-step 1:=sub_add_cancel ..
  rw [faceSites_list]; change [α,α+step 1,α+step 1+step 2,α+step 2,α].toFinset=_; rw [h1,h2,h3]; ext i; simp [α,x]; grind
lemma square_in (S:Finset Cover) (p: faceSites (wall M) ⊆ S) : restsOn {wall M} S := by
  intro x t; rw [mem_singleton.mp t]; exact p
lemma wall_in : faceSites (wall M) ⊆ early M:= Finset.subset_union_right
lemma early_in : M.ascY⊆early M := Finset.subset_union_left

lemma early_prior (x:Cover)(h:x∈ early M): x ≤ M.anchorY:= by
  rcases Finset.mem_union.mp h with a|a
  · exact (Finset.mem_Icc.mp a).2
  intro i; have he (j:Axis):0≤ Lattice.step j i (S:=ℤ) := by rw [step_apply]; split_ifs <;> norm_num
  rw [four] at a; simp only [mem_insert,mem_singleton] at a
  rcases a with e|e|e|e <;> rw [e] <;> simp only [Pi.sub_apply] <;> first | rfl | linarith [he 1,he 2]

lemma early_flat (x:Cover)(h:x∈ early M) : x 0=M.anchorY 0 := by
  apply le_antisymm (early_prior M x h 0)
  rcases Finset.mem_union.mp h with a|a
  · apply le_trans (_ : _ ≤ M.markY M.beams 0) ((Finset.mem_Icc.mp a).1 0)
    change _ ≤ M.markY M.beams (0:Fin 3).castSucc
    rw [M.west_v M.beams (0: Fin 3)]
    exact (M.west_v 0 (0: Fin 3)).le
  rw [four] at a; simp only [mem_insert,mem_singleton] at a
  rcases a with e|e|e|e <;> rw [e] <;> simp [show (0:Axis) ≠1 by decide, show (0:Axis)≠2 by decide]
end pane

section geometry
variable (Λ': Preparation) (s l' :ℕ)
lemma ball_eq (x:Cover) : stamp Λ' l' s x=collar Λ' l' s x:=by
  ext v; rw [stamp_abs]; show _ ↔ (collarLower Λ' l' s x≤v ∧ v≤ collarUpper Λ' l' s x); constructor
  · intro h; constructor <;> intro i
    · rw [lower_gauge]; linarith [(abs_le.mp (h i)).1]
    rw [upper_gauge]; linarith [(abs_le.mp (h i)).2]
  rintro ⟨a,b⟩ i; specialize a i; specialize b i; rw [lower_gauge] at a; rw [upper_gauge] at b; rw [abs_le]; constructor <;> linarith only [a,b]
lemma footprint_eq(S:Finset Cover): footprint Λ' l' s S=silhouette Λ' l' s S:= by
  unfold footprint silhouette; simp_rw [ball_eq]; rfl
end geometry

variable (s:ℕ)
local notation "N" => marks (timeMesh Λ)
local notation "κ" v:max => footprint Λ l s v
local notation "Δ" => whenly (timeMesh Λ) s 1
local notation "η" => gaugeMesh Λ s
local notation "Q" j:max => ruler (K).B * j
structure Setting (Z:Calibration)(w: Axis→ℤ)(A B: Finset Cover) : Prop where
  left (j : Axis): ∀ x∈A, x j + Z.ℓ ≤ ruler Z.B * w j
  right(j : Axis): ∀ x∈B, ruler Z.B * w j + ruler Z.B + Z.ℓ ≤ x j
namespace Setting
variable {w : Axis→ℤ} {S T: Finset Cover} (p:Setting (tent Y H) w S T)
local notation "δ" x:max => bell (timeMesh Λ) s x
include p
lemma before (u:RSpace)(h:u∈ κ S)(j:Axis) : u j≤ δ (w j):=by
  rw [Atlas.bell_norm,mul_comm (gaugeMesh Λ s)]
  obtain ⟨x,hx,h⟩:= silhouette_iff.mp ((footprint_eq Λ s l S) ▸ h)
  have he:= (p.left j x hx)
  calc
   _ ≤ gaugePosition Λ s x j+reserve Λ l*η := by linarith [(abs_le.mp (stamp_abs.mp h j)).2]
   _ = ((↑(x j+(reserve Λ l:ℤ))):ℝ)*η:= by unfold gaugePosition; simp only [Int.cast_add,Int.cast_natCast]; ring
   _ ≤ _:=mul_le_mul_of_nonneg_right (Int.cast_le.mpr he) (gaugeMesh_pos ..).le
lemma after (u:RSpace)(h:u∈ κ T)(j:Axis) : (δ (w j)) +(Δ:ℝ) ≤ u j:=by
  rw [show (Δ:ℝ) =δ (1:ℤ) from (natural_time (timeMesh Λ) s 1).symm,←bell_add,Atlas.bell_norm,mul_comm (gaugeMesh Λ s)]
  obtain ⟨x,hx,t⟩:= silhouette_iff.mp ((footprint_eq Λ s l T) ▸ h)
  have hp:ruler Λ.block*(w j+1) ≤ x j - (↑(reserve Λ l):ℤ):= le_sub_iff_add_le.mpr (by rw [_root_.mul_add,mul_one]; exact (p.right j x hx))
  refine le_trans (b:= (↑(x j - (↑(reserve Λ l):ℤ)):ℝ)*η) (mul_le_mul_of_nonneg_right (Int.cast_le.mpr hp) (gaugeMesh_pos ..).le) ?_
  have he:= (abs_le.mp (stamp_abs.mp t j)).1; unfold gaugePosition at he; simp only [Int.cast_sub, Int.cast_natCast]; linarith only [he]
lemma separated (u v:RSpace)(a:u∈ κ S)(b:v∈ κ T) : ∀ j:Axis, u j+ (Δ:ℝ) ≤ v j:=fun i=> le_trans (by gcongr; exact p.before Y H s u a i) (p.after Y H s v b i)
lemma disjoint : Disjoint (κ S) (κ T):= Set.disjoint_left.mpr (fun v a b=> by
  have h:=p.separated Y H s v v a b 0; linarith only [h,show 0 < (Δ:ℝ) from when_pos (timeMesh Λ) s 1 zero_lt_one])
lemma complete : Detached Λ l S T:= PhaseChoice.separatedPhys (has_footprint Λ l 0 S)
    (has_footprint Λ l 0 T) (Disjoint.preimage _ (p.disjoint Y H 0)) -- height independent
end Setting
end Siam
end YM.CF.Buffered.Afterglow.Tower.Selection.Home
open YM.CF.Buffered.Afterglow.Tower.Selection.Home.Siam
#print axioms early_prior
#print axioms Setting.separated
#print axioms footprint_eq
#print axioms Setting.complete

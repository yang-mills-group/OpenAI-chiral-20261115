import YM.SU5.Reconstruction.Chambers.Operator
import YM.SU5.Reconstruction.Chambers.Node
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 300000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
namespace Chambers
open Selected SlabMark MeshClock
open Schedule Schedule.Fixture Schedule.Compose
open SelectionAnalysis
set_option quotPrecheck false
local notation "D" => Domain Y H G
local notation "R" => RSpace
local notation "δ₁" => (timeMesh Λ)
local notation "M" => (MeshClock.marks (timeMesh Λ))
local notation "K₀" => tent Y H
local notation "Kₜ" => move (tent Y H)
variable {α : Type*}
variable (Gaps : Fixture (MeshClock.marks (timeMesh Λ)) α)
variable (A : α→Sky (tent Y H))

-- shield intervals BEFORE any motion. For compact marks can choose any larger endpoint windows.
def correctRegion (Gaps : Fixture (MeshClock.marks (timeMesh Λ)) α) (A : α→Sky (tent Y H)) (i:α) (j:Axis) :=
  A i∈D false (strip j (Gaps.low i j) ((Gaps.low i j:ℝ)+ (Gaps.width i j:ℝ)))

variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
variable (f : ∀ i, correctRegion Y H G Gaps A i j)
local notation "V₊" => flank j 0
local notation "F" => osValue Y H V G j C χ
local notation "λ₀" => OSvector Y H V G j C χ
local notation "P" => D false Set.univ
local notation "B₀" => mainsea Y H V G.history G.clipped j false C χ
local notation "Ω" => doorstep Y H V G.history G.clipped j false C χ
local notation "A'" i:max=> Kₜ (-(eject j (Gaps.low i j))) (A i)

include f V in
lemma register (i:α) : move (tent Y H) (-(eject j (Gaps.low i j))) (A i)∈ D false (strip j 0 (Gaps.width i j)) := by
  have h := moving Y H V G (-(eject j (Gaps.low i j))) (A i) (show A i∈Domain Y H G false (strip j (Gaps.low i j) _) from f i)
  rw [map_neg,coordinates_eject,strip_zero,add_sub_cancel_left] at h; exact h

noncomputable def signal (i:α) : (indoor Y H V G.history G.clipped j false C χ).Op :=
  stripOp Y H V G j C χ _ (Gaps.positive i j) (A' i) (register Y H V G _ A j f i)

lemma journey_cost (i:α) : Follows Y H V G j C χ (A' i) (Gaps.width i j) (signal Y H V G Gaps A j C χ f i) :=
  stripOp_follows ..

def generate (p:α→ placement Λ) (t:List α) : Sky (tent Y H) := (t.map (fun i=> move (tent Y H) (p i) (A i))).prod

@[simp] lemma generate_nil (p:α→placement Λ) : generate Y H A p []=1:=rfl
lemma generate_step (p:α→placement Λ) (t:List α) (i:α) : generate Y H A p (i::t) = (Kₜ (p i) (A i)) * generate Y H A p t := rfl
lemma generate_perm (p:α→placement Λ){t l:List α} (h:t.Perm l): generate Y H A p t=generate Y H A p l := (h.map _).prod_eq

local notation "T" => input (mainsea Y H V G.history G.clipped j false C χ) (signal Y H V G Gaps A j C χ f) Gaps
lemma bK (p : placement Λ) : (B₀).plane p = atEstate Y H V G.history G.clipped j false C χ p := rfl -- tune

section chrono
variable (p : α→ placement Λ) (q : placement Λ)
local notation "μ" t:max => (Kₜ t)
local notation "gen" => generate Y H A p

-- Step 2. Product (even spending overlaps by Detached where legal), as seen from q.
-- spectator movements all on common physical units. No extra births of spatial ticks.
lemma backward (t : List α) (h : Gaps.permission j false (enter p) (paste q) t) :
    ∃ g : Domain Y H G false (flank j 0),
      g.val = move K (-q) (generate Y H A p t) ∧ λ₀ g= T p q t Ω := by
  induction t generalizing q with
  | nil=> exact ⟨⟨1,domain_one ..⟩,(by rw [generate_nil,move_unit]),vacuum_ticket ..⟩
  | cons i t ih=>
    rw [permission_step] at h; obtain ⟨r,h⟩ := h
    have p1 : (0:ℝ) ≤ paste (Gaps.beginAt j p i-q) j := by rw [paste_sub,paste_begin]; exact r
    let a:=Gaps.beginAt j p i; let z:=Gaps.depart j p i; let w:=eject j (Gaps.width i j)
    rw [← paste_depart] at h
    obtain ⟨y,hy,v⟩ := ih z h
    obtain ⟨x,hx,e⟩ := (journey_cost Y H V G Gaps A j C χ f i).graph y
    let u : (μ (a-q)) x.val ∈ Domain Y H G false V₊ := later_frame Y H V G j _ _ x.property p1
    refine ⟨⟨_,u⟩,?_,?_⟩
    · change (μ (a-q)) x.val = _; rw [hx,hy]; simp_rw [generate_step,move_prod, move_sum]
      apply congrArg₂ (fun (a b:Sky (tent Y H))=>a*b)
      · rw [show a-q + -(eject j (Gaps.low i j)) = -q+p i from (by unfold a eject beginAt; abel)]
      · have e1 : z=a+w := rfl
        first | rw [show a-q+(w+ -z) = -q from (by rw [e1]; abel)] | rw [show (a-q+w)+ -z= -q from (by rw [e1]; abel)]
    rw [transported_ket Y H V G j C χ _ x.property (a-q) p1,e,v]
    unfold input; rw [roll_step]; rfl

lemma settles (t : List α) (h : Gaps.permission j false (enter p) (paste q) t) :
    ∃ h : generate Y H A p t ∈ Domain Y H G false Set.univ,
      osValue Y H V G j C χ ⟨generate Y H A p t,h⟩= inner ℂ Ω (T p q t Ω) := by
  obtain ⟨x,h,v⟩ := backward Y H V G Gaps A j C χ f p q t h
  have hh : x.val∈ Domain Y H G false Set.univ := domain_mono Y H G (Set.subset_univ _) x.property
  have hy : generate Y H A p t=(μ q) x.val := by rw [h,move_sum, add_neg_cancel,move_by_zero]
  refine ⟨(hy.symm ▸ (slides_univ .. ▸ moving Y H V G q x.val hh)),?_⟩
  rw [←v, FirstWindows.expectation]; apply Eq.trans _ (moving_value Y H V G j C χ q hh (slides_univ .. ▸ moving Y H V G q x.val hh))
  apply congrArg F; apply Subtype.ext; exact hy
end chrono

-- use all axes. old lenses require Arena Y chosen at that exact j.
end Chambers
end YM.CF.Buffered.Afterglow.Tower.FirstWindows

import YM.SU5.Reconstruction.Chambers.Plan
import YM.SU5.Reconstruction.Chambers.Analytic.Provided
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
open Selected SlabMark MeshClock Schedule SelectionAnalysis
open Schedule.Fixture Schedule.Compose
set_option quotPrecheck false
local notation "D" => Domain Y H G
local notation "R" => RSpace
variable {α : Type} [Fintype α]
variable (j₀ : Axis) (C : ∀ j : Axis, Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j₀ false (C j₀) →⋆ₐ[ℂ] ℂ)
local notation "F" => osValue Y H V G j₀ (C j₀) χ
local notation "I" j:max => indoor Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped j₀ false (C j₀) χ j (C j))
local notation "u'" j:max=> displacement Y H V G.history G.clipped j₀ false (C j₀) χ j (C j)
local notation "C'" j:max=> (C j)
local notation "W" j:max => fort Y H V G.history G.clipped j false (C j) (u' j)
local notation "K'" j:max=> mainsea Y H V G.history G.clipped j false (C j) (u' j)
local notation "S" j:max=> ride Y H V G.history G.clipped j false (C j) (u' j)
local notation "P" j:max=> peninsula Y H V G.history G.clipped j false (C j) (u' j)
local notation "Ωr" j:max=> doorstep Y H V G.history G.clipped j false (C j) (u' j)
local notation "Ωc" j:max=> vocation Y H V G.history G.clipped j false (C j) (u' j)

variable (A : α→Sky (tent Y H))
variable (B : Presentable Y H G A) (o : Axis→ List α) (t : Axis→ placement Λ)
local notation "Λ'" => prices Y H V G j₀ C χ A B o t
local notation "tI" => B.register.ready t o
variable (s : List α) (p0 : s.Nodup) (h : ∀ j:Axis,s.Perm (o j))
include s p0 h

lemma chamber_alive (i : Axis) (p : α→ RSpace) (v : p ∈ B.register.ready t o) :
    (∃ G₀ : (α × Axis→ℂ)→ℂ, AnalyticAt ℂ G₀ (PolyDisc.Revival.asC (uncurry p)) ∧
      (G₀ ∘ PolyDisc.Revival.asC)=ᶠ[𝓝 (uncurry p)] (prices Y H V G j₀ C χ A B o t i ∘ curry)) ∧
    AnalyticAt ℝ (prices Y H V G j₀ C χ A B o t i) p := Schedule.attained B.register o t p v (fun j:Axis=> W j)
      (fun j:Axis=> P j) (stripped Y H V G j₀ C χ A B) (fun j:Axis=> Ωc j) (fun j:Axis=> Ωc j) (fun _ a j=> full_continuous_extension Y H V G j₀ C χ A B o t s p0 h i j a)
lemma internal_analytic (i : Axis) : AnalyticOnNhd ℝ (prices Y H V G j₀ C χ A B o t i) (B.register.ready t o) :=
  fun _ a=> (chamber_alive Y H V G j₀ C χ A B o t s p0 h i _ a).2

omit [Fintype α] in
lemma changing_chamber (B' : Presentable Y H G A) (o' : Axis→List α)(t':Axis→placement Λ)
    (g : ∀ j:Axis,s.Perm (o' j)) (p q : Axis) : EqOn (prices Y H V G j₀ C χ A B o t p)
      (prices Y H V G j₀ C χ A B' o' t' q) (B.register.ready t o∩B'.register.ready t' o') := by
  apply close_on_open (B:=Set.range (Schedule.Fixture.enter (Γ:=marks (timeMesh Λ)) (α:=α))) (enters_dense (daylight (timeMesh Λ))) (prices_cont ..) (prices_cont ..) ((ready_open ..).inter (ready_open ..))
  rintro _ ⟨⟨a,b⟩,u,rfl⟩; rw [(prices_here Y H V G j₀ C χ A B o t s p0 h p u a).2,
    (prices_here Y H V G j₀ C χ A B' o' t' s p0 g q u b).2]

-- a common analytic section and, in each axis, its time-only half-space germ,
-- see `edge` for its further individual boundary clocks (not used here).
omit s p0 h in
noncomputable def WickSlice (j : Axis) (p : α→RSpace) (z : α→ℂ) : ℂ := inner ℂ (Ωc j)
  ((Schedule.curve (P j) B.register (stripped Y H V G j₀ C χ A B j) p (paste (t j)) z (((paste (t j) j):ℝ):ℂ) (o j)) (Ωc j))

omit s p0 h in
-- for temporal orders, even if only j-budget at projection-only extension.
lemma slice (j : Axis) (p : α→RSpace) (z : α→ℂ) (v : Schedule.ProperCone B.register j z (((paste (t j) j):ℝ):ℂ) (o j)) :
    DifferentiableAt ℂ (WickSlice Y H V G j₀ C χ A B o t j p) z ∧ ‖WickSlice Y H V G j₀ C χ A B o t j p z‖ ≤ Schedule.upright (stripped Y H V G j₀ C χ A B j) (o j) := by
  let R' := stripped Y H V G j₀ C χ A B j; let Z := Schedule.curve (P j) B.register R' p (paste (t j))
  let v' : W j:= Ωc j
  constructor
  · exact (innerSL ℂ v').differentiableAt.comp z
      (curve_diff (P j) B.register R' p (paste (t j)) (o j) v' z (fun _=>((paste (t j) j:ℝ):ℂ)) (z:=id) (fun i=>(differentiableAt_pi.mp (show DifferentiableAt ℂ id z from differentiableAt_id)) i ) (differentiableAt_const _) v)
  have ht:‖v'‖=1 := vocation_norm ..
  let a' := Z z (((paste (t j) j):ℝ):ℂ) (o j)
  unfold WickSlice; change ‖inner ℂ v' (a' v')‖ ≤ _
  apply le_trans (norm_inner_le_norm ..) _; rw [ht,one_mul]
  exact (spin_price (P j) B.register R' p (paste (t j)) _ _ _ v v').trans_eq (by rw [ht,mul_one])

-- exact link of ALL real values in strict chambers with these complex-time expressions.
omit [Fintype α] in
lemma all_currents (i : Axis) (p : α→RSpace) (u : p∈ B.register.ready t o) : ∀ j:Axis,
    WickSlice Y H V G j₀ C χ A B o t j p (fun t=> (p t j:ℂ))= prices Y H V G j₀ C χ A B o t i p := by
  intro j; unfold WickSlice
  rw [real_points (P j) B.register (stripped Y H V G j₀ C χ A B j) _ _ _ _ _ (u j)] -- tune order
  · exact full_continuous_extension Y H V G j₀ C χ A B o t s p0 h j i u
  all_goals intros; first | rfl | simp
end Chambers
end YM.CF.Buffered.Afterglow.Tower.FirstWindows

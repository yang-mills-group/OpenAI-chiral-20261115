import YM.SU5.Reconstruction.Chambers.Cost
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
local notation "Γ" => (MeshClock.marks (timeMesh Λ))
variable {α : Type*}
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
-- pay explicitly the **split into concrete supports** & COMPASS movie and CHAMBER.
structure Presentable (A : α→Sky (tent Y H)) where
  register : Fixture (marks (timeMesh Λ)) α
  shielded (j : Axis) (v : α) : correctRegion Y H G register A v j

variable (B : Presentable Y H G A) (o : Axis→ List α) (t : Axis→ placement Λ)
local notation "kA" j:max => signal Y H V G B.register A j (C j) (u' j) (B.shielded j)
local notation "E₀" j:max=> indoor Y H V G.history G.clipped j false (C j) (u' j)
local notation "J" => Domain Y H G false Set.univ

-- scalar defaults off the granted region; NO claims there. On granted region true anchored even reading.
noncomputable def score (p : α→ placement Λ) (s : List α) : ℂ := if h:generate Y H A p s∈ J then F ⟨generate Y H A p s,h⟩ else 0
noncomputable def raw (p : α → Selected.placement Λ) (j : Axis) : ℂ := inner ℂ (Ωr j)
  ((input (K' j) (kA j) B.register p (t j) (o j)) (Ωr j))
local notation "Jp" p:max s:max=> score Y H V G j₀ C χ A p s
local notation "uH" => raw Y H V G j₀ C χ A B o t
-- uniform agreement even on overlaps of strict and non-strict timing with another axis.
lemma raw_value (p : α→placement Λ) (j : Axis) (s : List α) (u : s.Perm (o j))
    (h : B.register.permission j false (Schedule.Fixture.enter p) (paste (t j)) (o j)) :
    generate Y H A p s∈ J ∧ raw Y H V G j₀ C χ A B o t p j = score Y H V G j₀ C χ A p s := by
  obtain ⟨a,b⟩:= settles Y H V G B.register A j (C j) (u' j) (B.shielded j) p (t j) (o j) h
  have he:= generate_perm Y H A p u
  unfold score raw; rw [he,dif_pos a,←b,os_across Y H V G]; exact ⟨a,rfl⟩

noncomputable def stripped (j:Axis) (i:α) : (fort Y H V G.history G.clipped j false (C j) (u' j)).Op :=
  corrected (K' j) ((kA j) i)
local notation "B'" j:max=> stripped Y H V G j₀ C χ A B j

/-- With every REAL time / spatial spectator argument, Euclidean points evaluation. Uses
 the same chosen compass space per channel and true spacetime translation units.* Acts only in
 **open overlap** for claim of simultaneous applicability. The expression elsewhere is a
 continuous function NOT authorized by this theorem. -/
noncomputable def prices (j : Axis) (p : α→RSpace) : ℂ := inner ℂ (Ωc j) ((pointsOp (P j) B.register (B' j) p (paste (t j)) (o j)) (Ωc j))
local notation "E" j:max=> prices Y H V G j₀ C χ A B o t j

lemma prices_cont (j : Axis) : Continuous (prices Y H V G j₀ C χ A B o t j) :=
  continuous_const.inner (cont_points (P j) B.register _ _ _ _ _ continuous_id continuous_const continuous_const)

variable (r : List α) (p0 : r.Nodup) (k₀ : ∀ j:Axis, r.Perm (o j))
include r p0 k₀
-- KEY to upgrading the input's chart comparison: uninterrupted multi-point, *different*
-- order in every coordinate. All on one law, inside its **time** Hilberts first, now even
-- all spatially continuous with no extra hypotheses, each computed in `fort`.
lemma prices_here (j : Axis) (p : α→placement Λ) (u : Schedule.Fixture.enter p ∈ B.register.ready t o) :
    generate Y H A p r ∈ J ∧ prices Y H V G j₀ C χ A B o t j (Schedule.Fixture.enter p) = score Y H V G j₀ C χ A p r := by
  have hc(p : α→placement Λ)(z : Schedule.Fixture.enter p ∈ B.register.ready t o)(j : Axis):=
    raw_value Y H V G j₀ C χ A B o t p j r (k₀ j) (B.register.permission_ge j _ _ _ (z j))
  let a (i:Axis) := (K' i); let v:= fun i: Axis=> Ωr i 
  have hp := Schedule.projected (j:=j) B.register (fun i:Axis=> I i) a (fun j:Axis=> S j) (fun i=>rfl)
    v v (fun i=> kA i) o t (fun p=> Jp p r) ((k₀ j).nodup p0) (fun p u j=> (hc p u j).2.symm) p u
  have hz:= vocate Y H V G.history G.clipped j false (C j) (u' j)
  refine ⟨(hc p u j).1, hp.trans ?_ |>.symm⟩
  let S' := (K' j); let k' := kA j
  have ht: funded S' (fun _=>S'.list) k' B.register p (t j) (o j) (Ωr j) =
      ((pointsOp (P j) B.register (B' j) (Schedule.Fixture.enter p) (paste (t j)) (o j)) (Ωc j) : W j).val :=
    career_all (S j) B.register S' rfl (daylight (timeMesh Λ)) (follows_road Y H V G.history G.clipped j false (C j) (u' j)) k' _ _ _ _ (Ωc j) hz.symm
  change inner ℂ (Ωr j) (funded S' _ _ _ _ _ _ _) = _; rw [ht,←hz]; rfl

lemma full_continuous_extension (j i : Axis) :
    Set.EqOn (prices Y H V G j₀ C χ A B o t j) (prices Y H V G j₀ C χ A B o t i) (B.register.ready t o) := by
  apply close_on_open (D':=B.register.ready t o) (enters_dense (α:=α) (daylight (timeMesh Λ))) (prices_cont ..) (prices_cont ..) (ready_open ..)
  rintro _ ⟨ht,p,rfl⟩; exact (prices_here Y H V G j₀ C χ A B o t r p0 k₀ j p ht).2.trans
    ((prices_here Y H V G j₀ C χ A B o t r p0 k₀ i p ht).2.symm)
end Chambers
end YM.CF.Buffered.Afterglow.Tower.FirstWindows

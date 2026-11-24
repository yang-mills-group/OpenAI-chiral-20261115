import YM.SU5.Reconstruction.Seams.Court
/-!
# Shutter lifetime j and order crossing at spectral window (PartII-B1)
- sequential costs at Real positive and negative Euclidean times on grid.
Uses all support conversions of same FirstWindows polynomial test space. -/
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
namespace LightBudget
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers
variable {J : Calibration} {q : Bool} {U W : Set RSpace}
local notation "D" => Domain Y H G false
local notation "Gt" => marks (timeMesh Λ)
local notation "K₀"=> tent Y H
variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "J₀"=> indoor Y H V G.history G.clipped j false C χ
local notation "C₀"=> saunters Y H V G.history G.clipped j false C χ
local notation "G₀"=> fort Y H V G.history G.clipped j false C χ
local notation "Ω₀"=> mainsea Y H V G.history G.clipped j false C χ
local notation "L"=> ride Y H V G.history G.clipped j false C χ
local notation "S"=> peninsula Y H V G.history G.clipped j false C χ
local notation "Π" x:max=> physicalKet Y H V G j C χ x
local notation "F"=> osValue Y H V G j C χ
local notation "A₀"=> flank j 0
set_option quotPrecheck false
local notation "P"=> (C₀).orthogonalProjectionOnto
local notation "θ"=> flipMark j K
local notation "ℜ" p:max=> Real.toNNReal (p:ℝ)
local notation "κ" p:max=> move K p
open Sail
local notation "Pr"=> bridgeEstate Y H V G j C χ
local notation "Vo"=> coreOs Y H V G j C χ
local notation "U"=> Domain Y H G false (flank j 0)
local notation "Ot"=> opCarries Y H V G j C χ
set_option quotPrecheck false
local notation "φ" t:max=> eject j t
-- base program
abbrev chron0 {Λ : Preparation} {J:Calibration} (j : Axis) (r z : marks (timeMesh Λ))(p a b x:Sky J) : Sky J := tab J (eject j (-r)) 0 (eject j z) (eject j r) (flipMark j J p) a b x

variable (p w: Domain Y H G false (flank j 0)) (tC : saunters Y H V G.history G.clipped j false C χ=⊤)
include tC
lemma opens_right {a b:Sky (tent Y H)} {u v:Gt} {A B: (J₀).Op}
    (hA:Follows Y H V G j C χ a u A)(hB:Follows Y H V G j C χ b v B)
    (r z:Gt)(hr: 0 ≤ (r:ℝ))(hz : u≤z)(hv:z+v≤r) :
    ∃ h:chron0 j r z p.val a b w.val∈ D univ,
      osValue Y H V G j C χ ⟨chron0 j r z p.val a b w.val,h⟩ = Sail.before (S) (ℜ (r:ℝ)) (Ot A) (Ot B) (Vo p) (Vo w) (u:ℝ) (v:ℝ) (z:ℝ):=by
  have y := show φ r - (φ z+φ v)=eject j (r-v-z) from ?_
  swap
  · rw [selectRay,sub_eq_add_neg, ← eject_neg,selectRay]; congr 1; abel
  obtain ⟨h,t⟩:= purchases Y H V G j C χ tC a b u v A B (φ (-r)) (φ r) 0 (φ z) p w hA hB (by simp [hr]) (by simp; exact hz) (by rw [y]; simp only [eject_at,AddSubgroup.coe_sub]; change 0≤_-_; linarith [show (z:ℝ)+(v:ℝ)≤r from hv])
  use h; rw [show (⟨chron0 ..,h⟩ : D univ) = ⟨tab K (φ (-r)) 0 (φ z) (φ r) (θ p.val) a b w.val, h⟩ from rfl]; rw [t, y, show (0: placement Λ) - eject j (-r)=eject j r from by rw [eject_neg]; abel,zero_add,show φ z-φ u= eject j (z-u) from (by simp only [sub_eq_add_neg, eject_neg, ← selectRay]),bridge_time,bridge_time,bridge_time, Sail.before_real,OS.Semigroup.swing,Real.coe_toNNReal (r:ℝ) hr]; rfl
lemma opens_left {a b:Sky (tent Y H)} {u v:Gt} {A B: (J₀).Op}
    (hA:Follows Y H V G j C χ a u A)(hB:Follows Y H V G j C χ b v B)
    (r z:Gt)(hr:0≤ (r:ℝ))(hz : z+v≤0)(hb:-r ≤ z)(hu:u≤r):
    ∃ h:chron0 j r z p.val a b w.val∈ D univ,
      osValue Y H V G j C χ ⟨chron0 j r z p.val a b w.val,h⟩ = Sail.after (S) (ℜ (r:ℝ)) (Ot A) (Ot B) (Vo p) (Vo w) (u:ℝ) (v:ℝ) (z:ℝ):=by
  have y : eject j z-eject j (-r) = eject j (r+z):= by rw [eject_neg,sub_neg_eq_add,selectRay,add_comm z]
  have x : (0:placement Λ)-(eject j z+eject j v)=eject j (-z-v):= by rw [selectRay,zero_sub, ← eject_neg]; congr 1; abel
  have r₀ : φ r -((0:placement Λ)+φ u)=eject j (r-u):= by rw [zero_add]; simp only [sub_eq_add_neg, eject_neg, ← selectRay]
  obtain ⟨h,t⟩:= purchases Y H V G j C χ tC b a v u B A (φ (-r)) (φ r) (φ z) 0 p w hB hA (by rw [y]; simp; linarith [show -(r:ℝ) ≤ z from hb]) (by rw [x]; simp only [eject_at,AddSubgroup.coe_sub,AddSubgroup.coe_neg]; linarith [show (z:ℝ)+(v:ℝ)≤0 from hz]) (by rw [r₀]; simp; exact hu)
  have h': chron0 j r z p.val a b w.val=tab K (φ (-r)) (φ z) 0 (φ r) (θ p.val) b a w.val:=by unfold chron0 tab; ac_rfl
  refine ⟨h'.symm ▸ h,?_⟩; rw [show (⟨chron0 ..,_⟩ : D univ)=⟨tab K (φ (-r)) (φ z) 0 (φ r) (θ p.val) b a w.val,h⟩ from Subtype.ext h',t]; rw [x,y,r₀,bridge_time,bridge_time,bridge_time, Sail.after_real,OS.Semigroup.swing,Real.coe_toNNReal (r:ℝ) hr]; rfl
end LightBudget
end YM.CF.Buffered.Afterglow.Tower.FirstWindows

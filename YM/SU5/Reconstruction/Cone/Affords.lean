import YM.SU5.Reconstruction.Cone.RootPrice
/-!
# Suffices to pay real Euclidean check in CF limit before taking the state

Also translates to a path check using `GroundExtension`. -/
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
open SlabMark MeshClock ConePrice Germ OS SelectionAnalysis
variable {J : Calibration} {q : Bool} {U W : Set RSpace}
local notation "V₀" => Domain Y H G false
local notation "D" => Domain Y H G true
local notation "Gt" => timeMesh Λ
variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "J₀" => indoor Y H V G.history G.clipped j false C χ
local notation "C₀" => saunters Y H V G.history G.clipped j false C χ
local notation "G₀" => fort Y H V G.history G.clipped j false C χ
local notation "Ω₀"=> mainsea Y H V G.history G.clipped j false C χ
local notation "L"=> ride Y H V G.history G.clipped j false C χ
local notation "S"=> peninsula Y H V G.history G.clipped j false C χ
local notation "Π" x:max=> physicalKet Y H V G j C χ x
local notation "F"=> osValue Y H V G j C χ
local notation "A₀"=> flank j 0
local notation "A"=> Ark.Ht Y H G.history.circuit j 0 false C
local notation "E₀"=> advance Y H V G.history.circuit j 0 false C
local notation "Z"=> ladder Y H V G.history.circuit j 0 false C
set_option quotPrecheck false
local notation "S₀"=> (clockdrive Y H V G.history.circuit j 0 false C).monoAxis j
local notation "ν" s:max=> actor Y H s G.history.circuit j 0 false C
local notation "Rχ" => ruler Y H V G j C
local notation "ν₀"=> prepaid Y H V G j C
local notation "Κv"=> courseValue Y H V G
local notation "θ"=> flipMark j K
local notation "kx"=> shop j K
local notation "ky"=> floor j K
local notation "Ms"=> gram j K
local notation "Ckt"=> Domain Y H G false Set.univ

section
local notation "Z₁" => driveAlgebra Y H V G.history G.clipped j false C
local notation "O" t:max=> coat Y H V G.history G.clipped j false C t
local notation "Q" i:max => shiftStamp Y H V G.history G.clipped j false C i
local notation "T"=> procession Y H V G.history G.clipped j false C χ
noncomputable def operator_stamp (p : placement Λ) (l : List (Trans j)) : driveAlgebra Y H V G.history G.clipped j false C :=
  l.foldr (fun i t=> shiftStamp Y H V G.history G.clipped j false C i (p i.val)*t) 1
@[simp] theorem operator_physical (p : placement Λ) (l : List (Trans j)) :
    (operator_stamp Y H V G j C p l).val=(Z).raw l (fun k=>p k.val) := by
  induction l with
  | nil=>rfl
  | cons i l ih=> rw [Alliance.raw_step,← ih]; rfl
@[simp] theorem buying_stamp (p : placement Λ) (l : List (Trans j)) :
    T (operator_stamp Y H V G j C p l) = (turnstile Y H V G.history G.clipped j false C χ).raw l (fun k=> p k.val) := by
  induction l with
  | nil=> change T 1=_; rw [map_one]; rfl
  | cons i l ih=> rw [show operator_stamp Y H V G j C p (i::l)=(Q i) (p i.val)*operator_stamp Y H V G j C p l from rfl,map_mul,ih]; rfl

noncomputable def trackCost (p : placement Λ) : driveAlgebra Y H V G.history G.clipped j false C :=
  (O ((coordinates Λ p j).toNNReal))*operator_stamp Y H V G j C p (look j)
@[simp] theorem track_cost_val (p : placement Λ) : (trackCost Y H V G j C p).val= ruler Y H V G j C p := by
  change (E₀ (coordinates Λ p j).toNNReal).comp (operator_stamp Y H V G j C p (look j)).val=_; rw [operator_physical]; rfl
lemma heat_track (p : placement Λ) : T (trackCost Y H V G j C p) = atEstate Y H V G.history G.clipped j false C χ p := by unfold trackCost; rw [map_mul,buying_stamp]; rfl
-- Second pressure payment is only TIME
lemma time_cost (p:placement Λ) : ruler Y H V G j C (onlyTime j p) = E₀ (coordinates Λ p j).toNNReal := by
  unfold ruler; rw [show coordinates Λ _ j=(coordinates Λ p j) from by rw [coord_at,quadrant]; rfl, show (fun i:Trans j=> onlyTime j p i.val)=0 from funext (fun i=> update_of_ne i.property ..),Alliance.raw_zero]; rfl

end

/-- Estimate in the whole Euclidean state before selection. Can prove by taking limits in real bills on
arbitrarily remote physical supported singlet tests from the `TwoShot` package. -/
def FirstShot (r e : ℝ) : Prop :=
  ∀ p : placement Λ, coordinates Λ p∈ ConePrice.CostDomain j e →∀ f:Sky (tent Y H), f∈D (flank j r) →
    ∀ (hx : gram j K (kx p f)∈ Ckt)(hv : gram j K (ky p f)∈ Ckt),
      (courseValue Y H V G ⟨gram j K (kx p f),hx⟩).re ≤ (courseValue Y H V G ⟨gram j K (ky p f),hv⟩).re

lemma preshot (x : Sky K) (u : x∈ V₀ A₀) (b : Ms x ∈ Ckt) : (courseValue Y H V G ⟨gram j K x,b⟩).re = ‖ν₀ ⟨x,u⟩‖^2 := by
  rw [show Κv ⟨gram j K x,b⟩=inner ℂ (ν₀ ⟨x,u⟩) (ν₀ ⟨x,u⟩) from (initial_pair Y H V G j C ⟨x,u⟩ ⟨x,u⟩).symm]; exact inner_self_eq_norm_sq (𝕜:=ℂ) _

lemma initial_test {x : Sky (tent Y H)} {p : placement Λ} (v : 0≤ coordinates Λ p j) (b : x∈ V₀ A₀)
    (k₁ : Ms (kx p x)∈ Ckt) (k₂ : Ms (ky p x)∈ Ckt) :
    (courseValue Y H V G ⟨Ms (kx p x),k₁⟩).re ≤ (courseValue Y H V G ⟨Ms (ky p x),k₂⟩).re ↔
      let f:= prepaid Y H V G j C ⟨x,b⟩
      ‖Rχ p f-Rχ (onlyTime j p) f‖ ≤ ‖f-Rχ (onlyTime j p) f‖ := by
  let u : 0 ≤ coordinates Λ (onlyTime j p) j:= by simp; exact v
  let l₁ := later_frame Y H V G j x p b v; let l₂:= later_frame Y H V G j x (onlyTime j p) b u
  rw [preshot Y H V G j C _ ((V₀ _).sub_mem l₁ l₂),preshot Y H V G j C _ ((V₀ _).sub_mem b l₂), sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  change ‖ν₀ (⟨move K p x,l₁⟩-⟨move K _ _,l₂⟩)‖ ≤ ‖ν₀ (⟨x,b⟩-⟨move K _ _,l₂⟩)‖ ↔ _
  rw [map_sub,map_sub,← initial_moves Y H V G j C x b p v,←initial_moves Y H V G j C x b (onlyTime j p) u] -- adjust

lemma first_suffices {b₀ e : ℝ} (p : 0≤b₀) (h : FirstShot Y H V G j b₀ e) {b : ℝ} (v : 0≤b) :
    TwoShot Y H V G j C χ b e := by
  refine (price_at_χ Y H V G j C χ v e).1 (fun z hz x=>?_)
  let W := trackCost Y H V G j C z - trackCost Y H V G j C (onlyTime j z)
  let U := 1-trackCost Y H V G j C (onlyTime j z)
  let T:= procession Y H V G.history G.clipped j false C χ
  have hx : ∀ x:A,‖W.val x‖ ≤ ‖U.val x‖ := by
    have hy:= advance_dense Y H V G j C b₀
    intro x; refine closure_minimal ?_ (isClosed_le ((show Continuous W.val from W.val.continuous).norm) ((show Continuous U.val from U.val.continuous).norm)) (hy x)
    rintro y ⟨f,r,s,b,rfl⟩; obtain ⟨g,g'⟩ := pressure_coverage Y H V G j z f r p (show coordinates Λ z∈ ConePrice.CostDomain j e from hz)
    let h₁:= domain_loose Y H G _ g; let h₂:= domain_loose Y H G _ g'
    change ‖(trackCost Y H V G j C z).val (ν₀ ⟨f,b⟩) - (trackCost Y H V G j C (onlyTime j z)).val _‖ ≤ ‖(ν₀ ⟨f,b⟩)-(trackCost Y H V G j C (onlyTime j z)).val _‖
    simp only [track_cost_val]; exact (initial_test Y H V G j C (show 0≤ coordinates Λ z j from hz.1.le) b h₁ h₂).1 (h z hz f r h₁ h₂)
  have hm:= ConePrice.encourages T hx x
  dsimp only [W,U,T] at hm
  rw [map_sub,map_sub,map_one,sub_apply,sub_apply,
    heat_track,heat_track,plaza] at hm; exact hm
end LightBudget
end YM.CF.Buffered.Afterglow.Tower.FirstWindows

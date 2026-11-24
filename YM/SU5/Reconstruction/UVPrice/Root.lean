import YM.SU5.Reconstruction.UVPrice.Soft
import YM.SU5.Reconstruction.UVPrice.Invest
import YM.SU5.Reconstruction.Cone.Affords
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
local notation "T"=> procession Y H V G.history G.clipped j false C χ
-- receipt exactly EARTH on THIS WHOLE chosen limit E and time stamp 8Mesh in each axis.
def RootSoft (r e δ:ℝ) : Prop:= ∀ (a:Axis)(_:a≠j)(z:marks (timeMesh Λ)),0<(z:ℝ)→ (z:ℝ)<e→ let t:= Picket.byStamp j a z
                                        ∀ f:Sky (tent Y H), f∈D (flank j r)→∀ (hx : Ms (kx t f)∈ Domain Y H G false univ) (hy : Ms (ky t f)∈ Domain Y H G false univ)(hz: Ms f∈ Domain Y H G false univ),
                                           ( Κv ⟨Ms (kx t f),hx⟩).re ≤ ( Κv ⟨Ms (ky t f),hy⟩).re+δ*( Κv ⟨Ms f,hz⟩).re
abbrev RootSmall (r:ℝ) : Prop:= ∀ j:Axis,∀ δ:ℝ,0<δ→ ∃ e>0, RootSoft Y H V G j r e δ
lemma part_cost {x : Sky (tent Y H)} {p : placement Λ} {δ:ℝ}(v : 0≤ coordinates Λ p j) (b : x∈ V₀ A₀)
    (k₁ : Ms (kx p x)∈ Ckt) (k₂ : Ms (ky p x)∈ Ckt) (k3:Ms x ∈ Ckt):
    (courseValue Y H V G ⟨Ms (kx p x),k₁⟩).re ≤ (courseValue Y H V G ⟨Ms (ky p x),k₂⟩).re + δ*(courseValue Y H V G ⟨Ms x,k3⟩).re ↔
      let f:= prepaid Y H V G j C ⟨x,b⟩
      ‖Rχ p f-Rχ (onlyTime j p) f‖^2 ≤ ‖f-Rχ (onlyTime j p) f‖^2+δ*‖f‖^2 := by
  let u : 0 ≤ coordinates Λ (onlyTime j p) j:= by simp; exact v
  let l₁ := later_frame Y H V G j x p b v; let l₂:= later_frame Y H V G j x (onlyTime j p) b u
  rw [preshot Y H V G j C _ ((V₀ _).sub_mem l₁ l₂),preshot Y H V G j C _ ((V₀ _).sub_mem b l₂), preshot Y H V G j C x b]
  change ‖ν₀ (⟨move K p x,l₁⟩-⟨move K _ _,l₂⟩)‖^2 ≤ ‖ν₀ (⟨x,b⟩-⟨move K _ _,l₂⟩)‖^2+ _ ↔ _
  rw [map_sub,map_sub,← initial_moves Y H V G j C x b p v,←initial_moves Y H V G j C x b (onlyTime j p) u]

lemma root_softens {b₀ δ e : ℝ} (p : 0≤b₀) (h : RootSoft Y H V G j b₀ e δ) {b : ℝ} (v : 0≤b) :
    Soft Y H V G j C χ b e δ := by
  refine (soft_pay Y H V G j C χ v).2 (fun a y hy hp x=> ?_)
  let z:= Picket.byStamp j a y; let hz : coordinates Λ z ∈ ConePrice.CostDomain j e:= Picket.starch (Ω₀) a y hy hp
  let W := trackCost Y H V G j C z - trackCost Y H V G j C (onlyTime j z)
  let U := 1-trackCost Y H V G j C (onlyTime j z)
  have hx : ∀ x:A,‖W.val x‖^2 ≤ ‖U.val x‖^2+δ*‖x‖^2 := by
    have hu:= advance_dense Y H V G j C b₀
    intro x; refine closure_minimal ?_ (t:={x:A|‖W.val x‖^2 ≤ ‖U.val x‖^2+δ*‖x‖^2}) (isClosed_le (by fun_prop) (by fun_prop)) (hu x)
    rintro yt ⟨f,r,s,b,rfl⟩; obtain ⟨g,g'⟩ := pressure_coverage Y H V G j z f r p hz
    let h₁:= domain_loose Y H G _ g; let h₂:= domain_loose Y H G _ g'; let h₃:= gram_covered Y H G j f s
    change ‖(trackCost Y H V G j C z).val (ν₀ ⟨f,b⟩) - (trackCost Y H V G j C (onlyTime j z)).val _‖^2 ≤ ‖(ν₀ ⟨f,b⟩)-(trackCost Y H V G j C (onlyTime j z)).val _‖^2+ _
    simp only [track_cost_val]; exact (part_cost Y H V G j C (show 0≤ coordinates Λ z j from hz.1.le) b h₁ h₂ h₃).1 (h a.val a.property y hy hp f r h₁ h₂ h₃)
  have hm:= ConePrice.prices_any T δ hx x
  dsimp only [W,U] at hm
  rw [map_sub,map_sub,map_one,sub_apply,sub_apply,
    heat_track,heat_track,plaza] at hm; exact hm
end LightBudget
end YM.CF.Buffered.Afterglow.Tower.FirstWindows

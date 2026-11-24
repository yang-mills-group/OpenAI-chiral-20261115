import YM.SU5.Reconstruction.Nymph.Pinnacle
/-!
# Continuity on native spaces (EVERY test ray) -- one test for restoration

This is only a new *criterion*, not claiming these estimates. In particular in
this same-law epoch we prove that from a light cone price on original `fort`,
no separate even-pitch taste can exist INSIDE that continuum part. And then a
potential tool: it remains only to find Reeh reconstruction/approximation by FAR
half-space probes, at both arbitrary resolutions & this selected state's own polar gram costs to pay it.
Horizontal pricing (Cone/Test previous route) even motions a possible verification
strategy. In CP1 cost it didn't unpack Reeh. Lanes are actual CP4 DAG.
-/
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
namespace Nymph
open SlabMark MeshClock PhaseChoice Chambers Germ
variable {J : Calibration} {y w : Set RSpace} {q : Bool}
local notation "L" => Λ.R.L
local notation "D" => Domain Y H G
set_option quotPrecheck false
open SelectionAnalysis OS.Semigroup
variable (iA:Axis) (R : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (χ : displayAlgebra Y H V G.history G.clipped iA false (R iA) →⋆ₐ[ℂ] ℂ)
local notation "P" => D false Set.univ
local notation "ν" => marks (dainty Λ)
local notation "c" j:max => displacement Y H V G.history G.clipped iA false (R iA) χ j (R j)
variable (j:Axis)
local notation "A" => indoor Y H V G.history G.clipped j false (R j) (c j)
local notation "Q" => ride Y H V G.history G.clipped j false (R j) (c j)
local notation "Ξ" => atEstate Y H V G.history G.clipped j false (R j) (c j)
local notation "X" => OSvector Y H V G j (R j) (c j)
local notation "T" => flank j 0
local notation "N" => Domain Y H G false (flank j 0)
local notation "V₀" => turnstile Y H V G.history G.clipped j false (R j) (c j)
local notation "B" i:max p:max => stride (tent Y H) i p
local notation "μ" j1:max => osValue Y H V G j1 (R j1) (c j1)
set_option quotPrecheck false
open Submodule InnerProductSpace LightBudget
variable (s: Trans j)
local notation "U" s:max=> (outfit Y H V G iA R χ j).crew s
local notation "L'" s:max=> (U s).lives (indoor Y H V G.history G.clipped j false (R j) (c j))
local notation "Z" s:max=> (L' s)ᗮ
local notation "Π₀" => (saunters Y H V G.history G.clipped j false (R j) (c j)).starProjection
local notation "D₁" s:max=> (eclipse Y H V G iA R χ j s)
local notation "λ₀" s:max=> (fourth Y H V G iA R χ j s)
set_option quotPrecheck false
local notation "Kk"=> (saunters Y H V G.history G.clipped j false (R j) (c j))
local notation "V₁"=> (Kk).orthogonalProjectionOnto
local notation "Hc"=> fort Y H V G.history G.clipped j false (R j) (c j)
local notation "Xt"=>physicalKet Y H V G j (R j) (c j)
local notation "Γ"=> compassKet Y H V G j (R j) (c j)
local notation "Qₜ"=> peninsula Y H V G.history G.clipped j false (R j) (c j)
local notation "W" d:max x:max=> (marksLane Y H V G iA R χ j s d x)
local notation "F" d:max x:max=> traceLane Y H V G iA R χ j s d x
-- use razor: FAR right physical test rays, at channel assembly stage. Don't need buy many insertions or full spacetime locality first. Reeh approximation on these is a way to get continuum spectrum/motion requirements. Again support fixed in PHYSICAL Units s.
noncomputable def recover (a:ℝ) : Submodule ℂ (indoor Y H V G.history G.clipped j false (R j) (c j)) := LinearMap.range ((physicalKet Y H V G j (R j) (c j)).comp (Submodule.inclusion (domain_mono Y H G (show (flank j 0 ∩ sideLand s.val a true) ⊆ flank j 0 from inter_subset_left))))
local notation "F₀" a:max=> recover Y H V G iA R χ j s a

def reehPrice : Prop := ∀ s:Trans j,∀ a:ℝ, Dense (recover Y H V G iA R χ j s a:Set (indoor Y H V G.history G.clipped j false (R j) (c j)))
local notation "Rc" => reehPrice Y H V G iA R χ j
-- colder: enough from right land, can take with many other spectators (but they WILL be theirs first), entire vac remains. Danger doesn't assert it.
lemma recover_lane (a:ℝ) (u:A) (p:u∈F a false) : u∈ (F₀ (a+1))ᗮ := by
 intro v hv; obtain ⟨f,rfl⟩ := LinearMap.mem_range.mp hv
 let g:N:=⟨f.val,domain_mono Y H G inter_subset_left (domain_loose Y H G _ f.property)⟩
 exact lane_shields Y H V G iA R χ j s a u p g (a+1) (by linarith) (domain_mono Y H G inter_subset_right (domain_loose Y H G _ f.property))
lemma meets_reeh (p : Rc) : L' s= ⊤ := by
 apply eq_top_iff.mpr; intro y _
 apply Submodule.starProjection_eq_self_iff.mp -- orientation? should mp? target mem first
 have hz : (D₁ s)=0 := by
   apply DFunLike.ext'; apply (attains_full_axis Y H V G iA j R χ).equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _); funext f; obtain ⟨a,v,-,-,e⟩ := cast_receives Y H V G iA R χ j s f
   exact (p s (v+1)).eq_zero_of_mem_orthogonal (recover_lane Y H V G iA R χ j s v _ e)
 rw [eclipse,sub_eq_zero] at hz
 change (λ₀ s) y=y
 rw [←hz]; rfl
lemma meet_early (p: Rc): saunters Y H V G.history G.clipped j false (R j) (c j)=⊤:=by
  apply eq_top_iff.mpr; intro y w; exact ((V₀).assembled _ _).2 fun i _=> larger_lives Y H V G iA R χ j i ((meets_reeh Y H V G iA R χ j i p).symm ▸ w)
section budget
variable (tF : ConePrice.Forward (peninsula Y H V G.history G.clipped j false (R j) (displacement Y H V G.history G.clipped iA false (R iA) χ j (R j))))
-- little full-vac test for recovering the spectrum assertion
include tF
lemma pays_both : Rc ↔ saunters Y H V G.history G.clipped j false (R j) (c j)=⊤:=by
  refine ⟨meet_early Y H V G iA R χ j, ?_⟩; intro hf s v u
  let J₁:= far Y H V G j (R j) (c j) s.val v true
  let K₁:= recover Y H V G iA R χ j s v
  let a:= (saunters Y H V G.history G.clipped j false (R j) (c j))
  have he:a=(⊤:Submodule ℂ A):=hf
  have hs : (V₁ u).val = u:= Submodule.starProjection_eq_self_iff.mpr (show u∈ saunters Y H V G.history G.clipped j false (R j) (c j) from hf.symm ▸ Submodule.mem_top)
  let v₀ : Hc→L[ℂ] A:= (saunters Y H V G.history G.clipped j false (R j) (c j)).subtypeL
  have h: v₀ '' (J₁:Set Hc) ⊆ K₁ :=by
    rintro _ ⟨(z : (fort Y H V G.history G.clipped j false (R j) (c j))),t,rfl⟩; obtain ⟨g,rfl⟩:= LinearMap.mem_range.mp t
    let x:=Submodule.inclusion (domain_mono Y H G (show flank j 0 ∩ _ ⊆ flank j 0 from inter_subset_left)) g
    refine LinearMap.mem_range.mpr ⟨g,?_⟩
    change Xt x= (Π₀) (Xt x)
    exact (Submodule.starProjection_eq_self_iff.mpr (show Xt x ∈ saunters Y H V G.history G.clipped j false (R j) (c j) from hf.symm ▸ Submodule.mem_top)).symm
  rw [← hs]; exact closure_mono h (mem_closure_image (f:=v₀) v₀.continuous.continuousAt (even_closer Y H V G j (R j) (c j) s.val s.property tF v true (V₁ u)))
end budget
end Nymph
end YM.CF.Buffered.Afterglow.Tower.FirstWindows

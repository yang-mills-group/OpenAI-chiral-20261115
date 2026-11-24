import YM.SU5.Reconstruction.Chambers.Torch
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

open CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet Py.Rate.Pannier
local notation "E₂"=> Bool→RSpace
variable (W₁ W₂ : Set RSpace) (s:ℕ)
section charge
variable (j : Axis) (S' : Finset Cover) (p q : Cover)
local notation "A"=>bufferedHull Λ l s (reflectedBox j 0 (streetBox K p S'))
local notation "B₁"=>bufferedHull Λ l s (streetBox K q S')
local notation "B'₁" => SpaceFor Λ A B₁
variable (R' : SpaceFor Λ (bufferedHull Λ l s (reflectedBox j 0 (streetBox (tent Y H) p S'))) (bufferedHull Λ l s (streetBox (tent Y H) q S')))
local notation "U₀" => R'.registerQ.ready R'.back (fun _=>[false,true])
local notation "A₀" x:max=> leg j p x
local notation "U₁" x:max=> reposition (tent Y H) q x
local notation "MP" => film Y H V G j₀ C χ A B₁ s R'
variable (d u₀ : ℕ) (f : Marks (tent Y H) true) (ζ: SU.Slot) (o : Cover) (δ : ℝ)
local notation "Pa"=> OnCharge Y H G j s p q S'
local notation "Mr" => relay Y H V G j₀ C χ s j S' p q R'
local notation "kA" h:max=> canon Y H V G j₀ C χ s j S' p q R' d u₀ f ζ o δ h

set_option maxHeartbeats 600000 in
lemma exhibits (h : LinkCheck Y H V G j (C j) (u' j) s p q S' ζ o u₀ d f δ) : Fuel Y H V G j₀ C χ s j S' p q R' d u₀ f ζ o δ h := by
  obtain ⟨a,b,x,y,u⟩:=h.see_basis
  obtain ⟨p1,p2,p3⟩:= witness_charge Y H V G j (C j) (u' j) s p q u h.apart
  let E(k:Axis) := Mr p3 k - Mr p1 k * Mr p2 k
  let f'(k:Axis) := (kA h) k
  have hs(k:Axis): AnalyticOnNhd ℝ (f' k) U₀:= torch_analytic Y H V G j₀ C χ A B₁ s R' (leg j p (fromStrict f)) (reposition K q (fromStrict f)) (insideAt_loose s h.first) (insideAt_loose s h.second) k
  have ht(k:Axis): AnalyticOnNhd ℝ (E k) U₀:= (torch_analytic Y H V G j₀ C χ A B₁ s R' _ _ p3.left p3.right k).sub ((torch_analytic Y H V G j₀ C χ A B₁ s R' _ _ p1.left p1.right k).mul (torch_analytic Y H V G j₀ C χ A B₁ s R' _ _ p2.left p2.right k))
  have ha(k:Axis): 1/32≤ ‖f' k 0‖:= at_site Y H V G j₀ C χ s j S' p q R' δ f h k
  have hz(k:Axis): 0< ‖E k 0‖:= division Y H V G j₀ C χ s j S' p q R' δ f h p1 p2 p3 u k
  have he:= R'.zero_fits
  have hp : IsOpen U₀ := ready_open ..
  have ht'(k k':Axis):Set.EqOn (E k) (E k') U₀  := by
    intro i uX; unfold E; simp only [Pi.sub_apply,Pi.mul_apply]; unfold relay; rw [torch_axis Y H V G j₀ C χ A B₁ s R' _ _ p1.left p1.right k k' uX, torch_axis Y H V G j₀ C χ A B₁ s R' _ _ p2.left p2.right k k' uX, torch_axis Y H V G j₀ C χ A B₁ s R' _ _ p3.left p3.right k k' uX]
  have hf(k k':Axis): Set.EqOn (f' k) (f' k') U₀ := torch_axis Y H V G j₀ C χ A B₁ s R' _ _ (insideAt_loose s h.first) (insideAt_loose s h.second) k k'
  let a' := ‖E j₀ 0‖/2; have bp : 0<a':=half_pos (hz j₀); let m := f' j₀* E j₀
  have hs' : AnalyticOnNhd ℝ m U₀:=(hs j₀).mul (ht j₀)
  have m0 : m 0≠0:=mul_ne_zero (norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (ha j₀))) (norm_pos_iff.mp (hz j₀))
  refine ⟨a,b,x,y,u,p1,p2,p3,a',bp,?_,?_⟩
  · filter_upwards [hp.mem_nhds he, ((ht j₀ _ he).continuousAt.norm.tendsto).eventually (le_mem_nhds (half_lt_self (hz j₀))), ((hs j₀ _ he).continuousAt.norm.tendsto).eventually (le_mem_nhds (lt_of_lt_of_le (by norm_num : (1:ℝ)/33<1/32) (ha j₀)))] with t u hv hu
    refine ⟨u,fun k'=>?_⟩; change 1/33 ≤ ‖f' _ _‖ ∧ _ ≤ ‖E _ _‖; rw [←hf j₀ k' u,← ht' j₀ k' u]; exact ⟨hu,hv⟩
  intro t pt; have hr: ∃ᶠ p' in 𝓝 t, m p' ≠0 := fun v=> m0 ((hs'.eqOn_zero_of_preconnected_of_eventuallyEq_zero (R'.registerQ.convex_ready ..|>.isPreconnected) pt (by simpa [EventuallyEq] using v)) he)
  apply (hr.and_eventually (hp.mem_nhds pt)).mono; rintro e ⟨a,u⟩; refine ⟨u,fun i=>?_⟩
  change f' j₀ e * E j₀ e ≠ 0 at a; rw [hf j₀ i u, ht' j₀ i u] at a
  exact ⟨left_ne_zero_of_mul a, sub_ne_zero.mp (right_ne_zero_of_mul a)⟩
end charge
end Chambers
end YM.CF.Buffered.Afterglow.Tower.FirstWindows

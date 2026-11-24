import YM.SU5.Reconstruction.Crease.Screen
import YM.SU5.Reconstruction.Crease.Habit
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers
open Anvil
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Ds" => Domain Y H G true
local notation "Gt" => marks (timeMesh Λ)
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "w" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (w i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (w i)
local notation "G₀" i:max=> fort Y H V G.history G.clipped i false (C i) (w i)
local notation "Ω₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (w i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (w i)
local notation "ℜ" p:max=> Real.toNNReal (p:ℝ)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (w i)
local notation "Vo" i:max=> coreOs Y H V G i (C i) (w i)
local notation "Os" i:max=> compassKet Y H V G i (C i) (w i)
local notation "D'" i:max=> Domain Y H G false (flank i 0)
local notation "Tx" => timeMesh Λ
local notation "Q" i:max=>Follows Y H V G i (C i) (w i)
local notation "X" i:max=> OSvector Y H V G i (C i) (w i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "m₁" => FirstWindows.move (tent Y H)
local notation "ℓ_"=>osValue Y H V G a (C a) χ
open BridgeClub Reflector
namespace Crease
variable (F: BoostBacking Y H V G C a χ)
variable (j z:Axis) (b:j≠z)
local notation "Ξ"=>parcelUp (S₀ j)
local notation "Λ₁"=>Sight Y H V G C a χ j
variable (U W: Set E4)
noncomputable def Wing : Set (G₀ j).Op:= {p|∃ (u v:Axis→Gt)(x:E4)(A:(G₀ j).Op), Λ₁ u v A ∧ ((fun y=> y+x) '' Reel j (fun i=>(u i:ℝ)) (fun i=>(v i:ℝ))) ⊆ U ∧ p= Ξ x A}
noncomputable def floor : Net (fort Y H V G.history G.clipped j false (C j) (w j)):= Auditorium (Wing Y H V G C a χ j U)
local notation "ℓ"=>Wing Y H V G C a χ j
local notation "ζ"=>floor Y H V G C a χ j
lemma sober (p:U⊆W) : ζ U≤ ζ W:=houseGrow (by rintro x ⟨u,v,y,A,h,t,rfl⟩; exact ⟨u,v,y,A,h,t.trans p,rfl⟩)
include F
lemma wing_star (x:(G₀ j).Op)(p:x∈ℓ U): star x∈ ℓ U:=by obtain ⟨u,v,y,A,h,t,rfl⟩:=p; exact ⟨u,v,y,star A,adjSight Y H V G C a χ F j u v A h,t,parcel_star ..⟩
lemma spacelike (d:TicketSeparation j U W) : ζ U≤ (ζ W).commutant := by
 apply houseFire (wing_star Y H V G C a χ F j U) (wing_star Y H V G C a χ F j W)
 rintro _ ⟨u,v,a₀,A,h,t,rfl⟩ _ ⟨u',v',b₀,B,k,d',rfl⟩
 rw [← atParcel,← atParcel]; apply (warrant Y H V G C a χ).law F j (Finset.univ.erase j) (Finset.notMem_erase _ _) u v u' v' A B (sight_guarded Y H V G C a χ j u v A h) (sight_guarded Y H V G C a χ j u' v' B k) _ _ (by simp [eyebrow]) (by simp [eyebrow])
 exact clearPay j _ _ _ _ a₀ b₀ (fun i p=>(h.1 i p).le) (fun i p=>(k.1 i p).le) (fun i p x q=> d i (t p) x (d' q))
-- unconditional with respect to W rank now. Regions Eu sewn.
variable (y:E4)
lemma translation_bound (p:(fun x=>x+y) '' U⊆ W) (x:(G₀ j).Op)(h:x∈ζ U) : Ξ y x∈ ζ W:= by
 refine rehouse (wing_star Y H V G C a χ F j U) (wing_star Y H V G C a χ F j W) (W:=Ξ (-y)) ?_ (V:=Ξ y) (parcel_went (S₀ j) y) (parcel_inv (S₀ j) y) (parcel_mul (S₀ j) y) x h
 rintro _ ⟨u,v,z,A,k,ht,rfl⟩; refine ⟨u,v,y+z,A,k,?_,(parcel_add ..).symm⟩; rintro _ ⟨x,t,rfl⟩; exact p ⟨_,ht ⟨x,t,rfl⟩,(show x+z+y=x+(y+z) by abel)⟩
lemma translation_cov (x:(G₀ j).Op): x∈ ζ U ↔ Ξ y x∈ ζ ((fun x=>x+y) '' U):=by
 refine ⟨translation_bound Y H V G C a χ F j U _ y (Set.Subset.refl _) x,fun p=>?_⟩
 rw [← parcel_went (S₀ j) y x]; refine translation_bound Y H V G C a χ F j _ U (-y) ?_ _ p
 rintro _ ⟨_,⟨i,h,rfl⟩,rfl⟩; simpa using h
include b
local notation "Φ"=> Flare Y H V G C a χ F j z b
lemma shadeParcel (x:(G₀ j).Op) : (Φ).shade (Ξ y x)= Ξ (turn j z y) ((Φ).shade x):= by unfold parcelUp; rw [Flash.shade_mul,Flash.shade_mul,orbitF, orbitF,turn_neg]
lemma reflection_bound (p: turn j z '' U⊆ W) (x:(G₀ j).Op)(h:x∈ζ U) : (Φ).shade x∈ ζ W:= by
 refine rehouse (wing_star Y H V G C a χ F j U) (wing_star Y H V G C a χ F j W) ?_ (Φ).back (Φ).back (Φ).shade_mul x h
 rintro _ ⟨u,v,y,A,k,ht,rfl⟩
 refine ⟨rebate z u v,v, turn j z y,(Φ).shade A,reflSight Y H V G C a χ F j z b u v A k,?_,shadeParcel ..⟩; rintro _ ⟨x,t,rfl⟩
 exact p ⟨turn j z x+y,ht ⟨_,(elective z u v) ▸ (remit j z b (rebate z u v) v x t),rfl⟩,by simp only [turn_add,turn_turn]⟩
lemma reflection_cov (x:(G₀ j).Op) : x∈ ζ U ↔ (Φ).shade x∈ ζ (turn j z '' U):=by
 refine ⟨reflection_bound Y H V G C a χ F j z b U _ (Set.Subset.refl _) x,fun p=>?_⟩
 rw [← (Φ).back x]; exact reflection_bound Y H V G C a χ F j z b _ U (by rintro _ ⟨_,⟨y,p,rfl⟩,rfl⟩; rwa [turn_turn]) _ p
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget

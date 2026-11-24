import YM.SU5.Reconstruction.Crease.Kiln
import YM.SU5.Reconstruction.Crease.Sensor
import YM.SU5.Reconstruction.Crease.Thicket
import YM.SU5.Reconstruction.Anvil.Component
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
local notation "Π₀" i:max=> opCarries Y H V G i (C i) (w i)
local notation "cΓ" i:max=> Tarp i
local notation "▷" i:max=> reversion (tent Y H) Λ i
variable (u v:Axis→ marks (timeMesh Λ))
-- genuine gauge singlet Market. all transverse clocks separate estimates.
def Sight (A:(G₀ j).Op):Prop:= (∀ i,i ≠ j → 0 < (v i:ℝ)) ∧
  ∃ (h:ℕ→Gt)(x:ℕ→Sky (tent Y H))(B:ℕ→ (J₀ j).Op),
    Slip Y H V G C a χ j x h B A ∧ (∀ n, x n∈ Ds ((cΓ j) (fun i=>(u i:ℝ)) (fun i=> (v i:ℝ)) (h n:ℝ))) ∧
    ∀ (i:Axis),i≠j→∃ Tm:ℕ→(J₀ i).Op, Perpendicular Y H V G i (C i) (w i) (v i) (u i) x Tm
local notation "L"=>Sight Y H V G C a χ j
lemma sight_guarded (A:(G₀ j).Op)(s: L u v A): Guarded Y H V G C a χ j (Finset.univ.erase j) u v A:=by
 obtain ⟨h,x,B,p,t,q⟩:=s.2; exact ⟨x,h,B,p,fun i=> q i (Finset.ne_of_mem_erase i.property)⟩
variable (x: ℕ→ Sky (tent Y H))(h:ℕ→marks (timeMesh Λ))
def rebate (z:Axis) (u v:Axis → Gt): Axis→Gt:=fun i=> if i=z then -(u i+v i) else u i
include b in
-- might complaint `omit` not incl.
lemma curator (x:Sky K)(h: Gt)(g:x ∈ Ds ((cΓ j) (fun i=>(u i:ℝ)) (fun i=>(v i:ℝ)) (h:ℝ))): ((θ z) x) ∈ Ds ((cΓ j) (fun i=>(rebate z u v i:ℝ)) (fun i=>(v i:ℝ)) (h:ℝ)):= by
 apply domain_mono Y H G _ (mirror_support Y H G z x g)
 rintro _ ⟨y,p,rfl⟩; constructor
 · rw [mirrorE, if_neg b]; exact p.1
 intro i q; have ht:= p.2 i q; by_cases hz:i=z
 · rw [mirrorE,if_pos hz]; rcases ht with ⟨h1,h2⟩; simp only [rebate,if_pos hz, AddSubgroup.coe_neg, AddSubgroup.coe_add, Set.mem_Icc]; change (u i:ℝ) ≤ y i at h1; constructor<;> linarith
 rw [mirrorE,if_neg hz]; simpa only [rebate,if_neg hz] using ht
include V in
lemma repo (x:Sky (tent Y H))(h:Gt)(g:x∈ Ds ((cΓ j) (fun i=>(u i:ℝ)) (fun i=>(v i:ℝ)) (h:ℝ))) : (▷ j) h x ∈ Ds ((cΓ j) (fun i=>(u i:ℝ)) (fun i=>(v i:ℝ)) (h:ℝ)):= by
 apply domain_mono Y H G _ (moving Y H V G _ _ (mirror_support Y H G j x g))
 rintro _ ⟨_,⟨y,p,rfl⟩,rfl⟩
 constructor
 · simp only [Pi.add_apply, mirrorE,if_true,coordinates_eject,eject_at,Set.mem_Icc]; rcases p.1 with ⟨hA,hB⟩; constructor<;> linarith
 intro i h'; simp only [Pi.add_apply, mirrorE,if_neg h',coordinates_eject,eject_away _ _ _ h', add_zero]; exact p.2 i h'
-- reflection on Mink real coordinates counterpart occupancy
include b
lemma remit (x:E4)(p: x∈Reel j (fun i=>(u i:ℝ)) (fun i=> (v i:ℝ))) : turn j z x∈ Reel j (fun i=>(rebate z u v i:ℝ)) (fun i=> (v i:ℝ)):=by
 constructor
 · simp [turn_at,p.1] -- test
 intro i q; rw [turn_at]; by_cases h:i=z
 · have t:=p.2 i q; rcases t with ⟨h1,h2⟩; simp only [rebate,if_pos h,if_pos (Or.inr h), AddSubgroup.coe_neg, AddSubgroup.coe_add, mem_Icc]; constructor<;>linarith
 simp only [q,h,false_or, if_false,rebate]; exact p.2 i q
omit b
lemma elective (z:Axis)(u v:Axis→Gt): rebate z (rebate z u v) v=u:=by ext1 i; unfold rebate; split_ifs <;> abel
local notation "D₀" i:max=> Perpendicular Y H V G i (C i) (w i) (v i) (u i) x
local notation "Ⅎ" i:max=> fun n=> reversion (tent Y H) Λ i (h n) (x n)
include F b
-- note vertical reversal sees Epoch h in a retimed clock whose Θ Monitor is paid in z too
lemma adjMonitor (B:ℕ→ (J₀ z).Op)(p: (D₀ z) B)(d:0<(v z:ℝ)) : ∃ S:ℕ→(J₀ z).Op,Perpendicular Y H V G z (C z) (w z) (v z) (u z) (Ⅎ j) S := by
 let α:=m₁ (eject z (-(u z)))
 have he(i:ℕ): α ((Ⅎ j) i)= (▷ j) (h i) (α (x i)):=by unfold reversion α; rw [echo_t Y H z j b.symm, move_sum,move_sum, add_comm]
 choose k0 h0 t0 using fun n=> otherFate Y H V G C a χ F z j b.symm _ _ d (B n) (p.beyond n)
 choose M Hx hM using fun i=> hiker Y H V G C a χ F z j b.symm _ _ d (k0 i) (h0 i) (h i)
 obtain ⟨e,v0⟩:=p.bounded
 refine ⟨M,(fun i=>(he i).symm ▸ (Hx i)), e,fun i=>?_⟩
 rw [hM]; exact (parcel_charge ..).trans (by rw [t0,Flash.shade_cost]; exact v0 i)
omit b
lemma adjSight (A:(G₀ j).Op)(p: L u v A): L u v (star A):=by
 obtain ⟨hz,h0,g,S,h,gp,T⟩:=p
 have hb: Limited atTop (fun i=> (Π₀ j) (star (S i))) (star A):= by simp_rw [op_star Y H V G C a χ F j]; exact star_Limited h.propitious
 refine ⟨hz,h0,fun i=>(▷ j) (h0 i) (g i), fun i=> star (S i),⟨(fun n=> fromBack Y H V G C a χ j _ _ (h.stays n) (h.phase n)),h.phase,h.short,hb⟩,(fun i=> repo Y H V G j u v _ _ (gp i)),fun i q=>?_⟩
 obtain ⟨B,S₁⟩:= T i q; exact adjMonitor Y H V G C a χ F j i q.symm u v g h0 B S₁ (hz i q)
include b
local notation "J₁"=> Flare Y H V G C a χ F j z b
lemma reflSight (A:(G₀ j).Op)(p:L u v A): L (rebate z u v) v ((J₁).shade A):=by
 obtain ⟨hz,h0,g,S,h,gp,T⟩:=p
 choose K₁ e t using fun i=> otherFate Y H V G C a χ F j z b (g i) (h0 i) (h.phase i) _ (h.stays i)
 have eb: Limited atTop (fun i=>(Π₀ j) (K₁ i)) ((J₁).shade A):=by simp_rw [t]; exact shade_Limited (J₁) h.propitious
 refine ⟨hz,h0,(fun i=> (θ z) (g i)), K₁, ⟨e,h.phase,h.short, eb⟩,fun i=> curator Y H G j z b u v _ _ (gp i),fun i q=> ?_⟩
 obtain ⟨T0,k0,S0,ru⟩:= T i q; by_cases π:i=z
 · subst i
   rw [rebate,if_pos rfl]
   let U₁(n:ℕ):= m₁ (eject z (-(u z))) (g n)
   have he(n): (▷ z) (v z) (U₁ n)= m₁ (eject z (u z+v z)) ((θ z) (g n)):= by unfold reversion U₁; rw [flipped_moves,reverse_eject,neg_neg,move_sum,selectRay]; rw [add_comm]
   refine ⟨fun i=> star (T0 i), (fun i=> ?_), S0, ?_⟩
   · change Follows _ _ _ _ _ _ _ (m₁ (eject z (- -(u z+v z))) ((θ z) (g i))) (v z) (star (T0 i)); rw [neg_neg,← he]; exact fromBack Y H V G C a χ z _ _ (k0 i) (hz z q)
   change ∀ i:ℕ, ‖(Π₀ z) (star (T0 i))‖≤ S0; simpa only [op_star Y H V G C a χ F z,norm_star] using ru
 choose M hm pM using fun n=> otherFate Y H V G C a χ F i z π _ _ (hz i q) _ (k0 n)
 rw [rebate,if_neg π]; refine ⟨M,(fun n=> ?_), S0, fun n=>?_⟩
 · change Follows _ _ _ _ _ _ _ (m₁ (eject i (-(u i))) ((θ z) (g n))) (v i) (M n)
   rw [← echo_t Y H i z π]; exact hm n
 -- i renamed
 rw [pM, Flash.shade_cost]; exact ru n -- tune duplicate shadowing
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget

import YM.SU5.Reconstruction.Crease.Radio
import YM.SU5.Reconstruction.Crease.Ghost
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
local notation "T" i:max=> opCarries Y H V G i (C i) (w i)
-- stars
include F
lemma op_star (A:(J₀ j).Op): (T j) (star A)= star ((T j) A):= by
   ext1 v; apply ext_inner_left ℂ; intro y; rw [show star ((T j) A)= ((T j) A).adjoint from rfl, ContinuousLinearMap.adjoint_inner_right]
   change inner ℂ y.val (((T j) (star A)) v).val=inner ℂ (((T j) A) y).val v.val; rw [carries_full Y H V G j (C j) (w j) (F.present j),carries_full Y H V G j _ _ (F.present j)]; exact ContinuousLinearMap.adjoint_inner_right ..
local notation "mΘ" => Flare Y H V G C a χ F j z b
variable (f:Sky (tent Y H))(t: marks (timeMesh Λ))(p:0<(t:ℝ))(A:(indoor Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op) (h: Follows Y H V G j (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j)) f t A)
omit F
include b
-- shift helpers
lemma echo_t (x: Gt)(g:Sky K) : (θ z) (m₁ (eject j x) g)=m₁ (eject j x) ((θ z) g):= by rw [flipped_moves,reverseAway z j b] -- echo time and many orientations
include F p h
lemma otherFate : ∃ B:(J₀ j).Op,(Q j) ((θ z) f) t B ∧ (T j) B=(mΘ).shade ((T j) A):=by
 let e: (θ z) f∈ D (strip j 0 (t:ℝ)):= domain_mono Y H G (by rintro _ ⟨x,q,rfl⟩; change _≤ mirrorE z 0 x j∧ mirrorE z 0 x j≤_; rw [mirrorE,if_neg b]; exact q) (mirror_support Y H G z f h.pose)
 obtain ⟨B,v⟩:= fits Y H V G j (C j) (w j) t p _ e
 refine ⟨B,v,?_⟩; apply chamberEd; intro x
 let y: D' j:= ⟨_,sidestamp Y H G j z b x⟩; obtain ⟨s,u,d⟩:=voice_follows Y H V G j (C j) (w j) (F.present j) v x; obtain ⟨s',w0,y0⟩:= voice_follows Y H V G j _ _ (F.present j) h y
 rw [Flash.shade_at,flare_cash Y H V G C a χ F j z b x y rfl,← d,← y0]; apply Eq.symm (flare_cash Y H V G C a χ F j z b s' s _)
 rw [u,w0,flipMark_mul,echo_t Y H j z b, show y.val=(θ z) x.val from rfl,mirror_twice]
local notation "S₁"=> S₀ j
local notation "ν"=>Picket.trans (S₀ j)
lemma hiker (x: Gt): ∃ B:(J₀ j).Op,(Q j) (m₁ (eject z x) f) t B ∧ (T j) B=parcelUp (S₀ j) ((x:ℝ) • basis z) ((T j) A):=by
 let u:= eject z x; have ht: coordinates Λ u j=0:= by simp [u,b]
 let g:= m₁ u; have e:g f∈ D (strip j 0 (t:ℝ)):= domain_mono Y H G (by rintro _ ⟨x,q,rfl⟩; change _ ≤ x j+ coordinates Λ u j ∧ x j+ coordinates Λ u j ≤ _; simpa [ht] using (show 0≤ x j ∧ x j≤ (t:ℝ) from q)) (moving Y H V G u f h.pose) -- slides order tune
 obtain ⟨B,v⟩:= fits Y H V G j (C j) (w j) t p _ e
 refine ⟨B,v,Eq.symm (inParcel _ _ _ ?_)⟩; apply chamberEd; intro y
 let R(q: D' j) : D' j:= ⟨_,later_frame Y H V G j q.val u q.property ht.ge⟩; have he(q:D' j): (Pr j) u ((Vo j) q)= (Vo j) (R q) := (voice_move Y H V G j (C j) (w j) (F.present j) u q ht.ge (R q).property).symm
 obtain ⟨k1,p1,v1⟩:=voice_follows Y H V G j _ _ (F.present j) v (R y); obtain ⟨k0,p0,v0⟩:= voice_follows Y H V G j _ _ (F.present j) h y
 simp only [mul_apply_eq_comp,←castSpace Y H V G C a χ j b.symm x]; rw [he,← v1,←v0,he]; apply congrArg; apply Subtype.ext
 rw [p1]; change _=m₁ u k0.val; rw [p0,move_prod]; change _* m₁ (eject j t) (m₁ u y.val)=_; rw [move_sum,move_sum,add_comm u]; -- rho order
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget

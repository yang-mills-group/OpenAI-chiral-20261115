import YM.SU5.Reconstruction.Quartz.WindUp
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option linter.unusedSectionVars false
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
open CrossedFrame
local notation "U"=>flank j 0∩flank z 0
local notation "Λ₁" i:max=>onceLens Y H V G C a χ i
local notation "𝔐" i:max=> opCarries Y H V G i (C i) (w i)
variable {D₀:Hilbert} (Z : Clasp D₀ (fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))) (fort Y H V G.history G.clipped z false (C z) (displacement Y H V G.history G.clipped a false (C a) χ z (C z))))
variable (p:Quarter Y H V G C a χ j z b.symm Z)
open YM.Quartz YM.Quartz.Waltz YM.Quartz.Ship
local notation "Qv"=> Picket.quarter j z
local notation "Lvl" i:max=>floor Y H V G C a χ i
local notation "Uj" i:max=>Picket.trans (S₀ i)
local notation "Oh" i:max=>parcelUp (S₀ i)
local notation "Wj"=> Wedge j z
local notation "Wz"=> Counter z j
local notation "M₁"=> (Lvl j) Wj
local notation "M₂"=> (Lvl z) Wz
local notation "ι"=> Z.look.conjStarAlgEquiv
local notation "Cj" i:max k:max bj:max=> Creased Y H V G C a χ F i k bj
noncomputable def Affinity := (Ship.join (M₁) (Pull Z.look M₂))
-- named condition.El.R.Seek.
variable (r:Creased Y H V G C a χ F z j b.symm)
local notation "ℒ" => Affinity Y H V G C a χ j z Z
local notation "Ω"=> Ω₀ j
local notation "Γ"=> volunteer Y H V G C a χ j z
include p F
lemma tithes(A:(G₀ j).Op) (q:A∈ ℒ) (x:E4)(h: Waltz.stowed j z x) : (Oh j) x A∈ ℒ:= by
 obtain ⟨u,v⟩:= (joining ..).1 q
 apply (joining ..).2 ; refine ⟨?_,?_⟩
 · exact translation_bound Y H V G C a χ F j Wj _ x (by rintro _ ⟨i,w',rfl⟩; exact sun_plus w' h) _ u
 apply (pulling ..).2; rw[← carries_shift Y H V G C a χ j z b Z p]
 refine translation_bound Y H V G C a χ F z (Counter z j) _ (Qv x) ?_ _ ((pulling ..).1 v)
 rintro _ ⟨i,t,rfl⟩; apply sun_min t; have e:= Picket.quarter_gear b.symm x
 unfold stowed; rw [PiLp.neg_apply,PiLp.neg_apply,e.1,e.2.1,neg_neg,abs_neg]; exact h
include r
local notation "𝔐"=> parish ℒ (Ω₀ j)
lemma crewing (h:CrewCost Y H V G C a χ j z) : owns_it ℒ (Ω₀ j):= by
 let P:= 𝔐; let v:= tithes Y H V G C a χ F j z b Z p
 let S:=(S₀ j); let X₁:= Γ
 have u0: Picket.Paces z S:=  ((grants Y H V G j _ _ (le_refl (0:ℝ)) zero_lt_one (((real_boost_purchase Y H V G C a χ (le_refl (0:ℝ)) (show 0<(1:ℝ) from zero_lt_one)).2 F).purchases j)).2 z b.symm)
 intro x; refine closure_minimal ?_ (Submodule.isClosed_topologicalClosure _) (h x)
 let q:= stay_everywhere b.symm S ℒ Ω (fun _=> compass_origin ..) v u0
 refine Submodule.span_le.mpr ?_; rintro _ ⟨A,t,y,rfl⟩ -- shape image maybe
 obtain ⟨s,d,e⟩:= chief Y H V G C a χ F j z b Z p r A t
 let i:E4:= s• basis z; let Y':=(Oh j) i A; have he:Y'∈ ℒ:= (joining ..).2 ⟨translation_bound Y H V G C a χ F j Wj _ i (by rintro _ ⟨x,p1,rfl⟩; exact sun_plus p1 (plus_step b.symm s d.le)) _ (awake_cl Y H V G C a χ F j z b Z p A t),(pulling ..).2 ?_⟩; swap
 · unfold Y' i; rw[← carries_shift Y H V G C a χ j z b Z p, quarterCare Y H V G C a χ j z b Z p]; exact e
 apply q y; apply Eq.subst (?_: (Uj j) (-i) (Y' Ω)=A Ω ) (q (-i) (transport_home ℒ Ω Y' he)); unfold Y'; rw [keepsLaw Y H V G C a χ j]; exact DFunLike.congr_fun (mail_inv S i) (A Ω)
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget

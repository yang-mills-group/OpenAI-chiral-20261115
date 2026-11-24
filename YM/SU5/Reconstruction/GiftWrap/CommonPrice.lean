import YM.SU5.Reconstruction.GiftWrap.Thru
/-! # Core: Closed multi-portrait Rank spanner -/
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
open CrossedFrame
local notation "U"=>flank j 0∩flank z 0
local notation "Λ₁" i:max=>onceLens Y H V G C a χ i
local notation "Π" i:max=> opCarries Y H V G i (C i) (w i)
variable {D₀:Hilbert} (Z : Clasp D₀ (fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))) (fort Y H V G.history G.clipped z false (C z) (displacement Y H V G.history G.clipped a false (C a) χ z (C z))))
variable (p:Quarter Y H V G C a χ j z b.symm Z)
local notation "Tm" i:max=> Picket.trans (S₀ i)
local notation "Ω" i:max=> Ω₀ i
local notation "Sq" => (S₀ j)
namespace Boots
local notation "lu" x:max=> (Tm j) ((x:ℝ) • basis z)
local notation "BC" => parcelUp Sq
open Lens Sail
local notation "lz" T₁:max => (Tm z) ((T₁:ℝ) • basis j)
local notation "N" => reserves Y H V G C a χ j z Z
local notation "Φ₀" x:max=> far Y H V G j (C j) (w j) z x false
variable {x: Sky (tent Y H)} (d v0 s t: marks (timeMesh Λ))
variable (A:(indoor Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op)
  (A':(indoor Y H V G.history G.clipped z false (C z) (displacement Y H V G.history G.clipped a false (C a) χ z (C z))).Op)
variable (f0: Follows Y H V G j (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j)) x s A)
  (f1: Follows Y H V G z (C z) (displacement Y H V G.history G.clipped a false (C a) χ z (C z)) (FirstWindows.move (tent Y H) (eject z (-d)) x) v0 A')
variable (c :ℝ≥0)
variable (Q': Set E4)(c₀:ℝ)
variable (A0:(fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op)
variable {T':ℕ→(fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op}
variable (p0 : ∀ n, Script (peninsula Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))) (floor Y H V G C a χ j Q') (T' n) (Real.toNNReal (s:ℝ)) c)
  (p1 : Limited atTop T' A0)
  (qW:∀ x∈Q',|x j|+x z ≤ c₀)
local notation "Tt"=> (ℜ t)
local notation "Aq"=> (Π j) A
variable (u v:Axis→marks (timeMesh Λ)) (L : (fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op)
local notation "η" => u z+v z+(u z-(d+v0))
local notation "Θ₀" x:max=> (S₀ j).E x
variable (eL: Sight Y H V G C a χ j u v L)(g:d+v0<u z)(a₁:c₀+1 < (u z:ℝ))
local notation "ℓ" => ℜ s
section wall
-- spaces needed for extension.Cost orientation j. Note Parliament price for *already* booked script
noncomputable def congruenceSeat: Submodule ℂ (G₀ j):= ⨅ t:ℝ≥0, LinearMap.ker ((A0 - (Π j) A).comp ((S₀ j).E t)).toLinearMap
local notation "S'"=> congruenceSeat Y H V G C a χ j A A0
lemma truthful (y:G₀ j) : y∈ S' ↔ ∀ t:ℝ≥0,A0 ((Θ₀ t) y)=Aq ((Θ₀ t) y):= by
 unfold congruenceSeat; rw [Submodule.mem_iInf]; exact forall_congr' fun t=> sub_eq_zero
lemma kept : IsClosed (S':Set (G₀ j)):= by unfold congruenceSeat; rw [Submodule.coe_iInf]; exact isClosed_iInter fun i=> isClosed_eq ((A0- (Π j) A).comp (Θ₀ i)).continuous continuous_const
noncomputable def wallSpace (x:Gt) := (S' ⊓ N x).topologicalClosure
local notation "ΩX" => wallSpace Y H V G C a χ j z Z A A0
noncomputable def fellowship:=⨅ x:Gt, ΩX x
local notation "FP"=> fellowship Y H V G C a χ j z Z A A0
lemma closedFellowship : IsClosed (FP:Set (G₀ j)):= by unfold fellowship; rw [Submodule.coe_iInf]; exact isClosed_iInter fun i=> Submodule.isClosed_topologicalClosure _
lemma sickle : FP ≤ S':= le_trans (iInf_le (ΩX) 0) (Submodule.topologicalClosure_minimal _ (show S' ⊓ N (0:Gt) ≤ S' from inf_le_left) (kept ..))
-- Momentum fellowship
lemma mapclosure_to (I J:Submodule ℂ (G₀ j))(h:IsClosed (J:Set (G₀ j)))(B:(G₀ j).Op)(q:MapsTo B (I:Set (G₀ j)) (J:Set (G₀ j))) : MapsTo B I.topologicalClosure J:= fun i p=> show i∈ B⁻¹' (J:Set (G₀ j)) from closure_minimal q (h.preimage B.continuous) p  -- tune
lemma mapclosure_ran (I J:Submodule ℂ (G₀ j))(B:(G₀ j).Op)(q:MapsTo B (I:Set (G₀ j)) (J:Set (G₀ j))) : MapsTo B I.topologicalClosure J.topologicalClosure:= mapclosure_to Y H V G C a χ j I J.topologicalClosure (Submodule.isClosed_topologicalClosure _) B (fun i p=> Submodule.le_topologicalClosure _ (q p))
include F p
lemma followUnit (e:A0 (Ω j)=Aq (Ω j)) : Ω j ∈ FP:= by
 rw [fellowship, Submodule.mem_iInf]; exact fun x=>Submodule.le_topologicalClosure _ (show Ω j∈ S'⊓N x from ⟨(truthful ..).2 (fun t=>by rw[seat_cools]; exact e), boardVac Y H V G C a χ F j z b Z p x⟩)
lemma wallCools (x:Gt)(t':ℝ≥0) : MapsTo (Θ₀ t') (ΩX x) (ΩX x):=by
 have h (t:Gt)(ht: 0≤ (t:ℝ)) : MapsTo (Θ₀ (ℜ t)) (S'⊓N x: Submodule ℂ (G₀ j)) (S'⊓ N x:Submodule ℂ (G₀ j)):= by
   rintro i ⟨q,b'⟩; refine ⟨(truthful ..).2 (fun w0=>?_), wallHeat Y H V G C a χ F j z b Z p x t ht i b'⟩; have hx:=(truthful ..).1 (show i∈S' from q) (w0+ℜ t); rw [(S₀ j).time] at hx; exact hx
 intro y hy; apply radiatory (A:=Tx) (W:={i:ℝ≥0| ((S₀ j).E i) y∈ ΩX x}) ((Submodule.isClosed_topologicalClosure _).preimage ((S₀ j).continuousE y)) _ t'; exact fun i p'=> (mapclosure_ran Y H V G C a χ j _ _ _ (h i p'.le) hy) -- helper
lemma cool (u:ℝ≥0) (q:G₀ j) (v:q∈ FP) : (Θ₀ u) q∈ FP:= (Submodule.mem_iInf (ΩX)).mpr fun i=> wallCools Y H V G C a χ F j z b Z p A A0 i u ((Submodule.mem_iInf (ΩX)).1 (show _ from v) i)
local notation "P'" k:max=> (S' ⊓ N k).topologicalClosure
-- using fromLocus etc
include f0 f1 qW p0 p1 eL
lemma wallSight (κ:Gt)(s0:0≤ (s:ℝ)) (x':G₀ j)(hx:x'∈FP) : L x'∈ ΩX κ:=by
 let d':= max (κ:ℝ) (max ↑(d+v0:Gt) (c₀+1)); let A₀:= d'-(u z:ℝ)
 apply freeing Sq (ΩX κ) (Submodule.isClosed_topologicalClosure _) b.symm A₀ (marks Tx) (daylight Tx) (F.forward j) L x' Tx -- tune order
 intro r hr ht t₀ w' dT dw; apply wallCools Y H V G C a χ F j z b Z p A A0 κ t₀
 let i:Gt:=⟨r,hr⟩; let o:=u+eject z i; let j' := o z-(d+v0); let ℓt:=(o z+v z+j')
 have vL:(o z:ℝ)=(u z:ℝ)+r:= by unfold o; rw[Pi.add_apply,eject_at]; rfl
 have t₁: d'< (o z:ℝ):= by rw[vL]; linarith [show d'-(u z:ℝ)<r from ht]
 have tκ: κ< o z:=(show (κ:ℝ)< (o z:ℝ) from (le_max_left ..).trans_lt t₁); have ts: d+v0<o z:=(show (↑(d+v0:Gt):ℝ)< (o z:ℝ) from ((le_max_left ..).trans (le_max_right ..)).trans_lt t₁)
 have tz: c₀+1< (o z:ℝ):= ((le_max_right ..).trans (le_max_right ..)).trans_lt t₁
 let B:= BC (r • basis z) L; have Pq:= aheadSight Y H V G C a χ F j z b u v i L eL
 refine mapclosure_to Y H V G C a χ j (S' ⊓ N ℓt) _ ?_ B ?_ (wallCools Y H V G C a χ F j z b Z p A A0 ℓt w' ((Submodule.mem_iInf (ΩX)).1 (show _ from hx) ℓt)) -- refine goal check
 · exact Submodule.isClosed_topologicalClosure _
 · rintro x'h ⟨hx,hq'⟩; refine Submodule.le_topologicalClosure _ ?_
   refine (show B x'h∈ S'⊓N κ from ⟨(truthful ..).2 (fun t' => ?_), accost Y H V G C a χ F j z b Z p κ o v tκ B Pq (byWall Y H V G C a χ F j z b Z p (o z+v z) ℓt (le_add_of_nonneg_right (sub_nonneg.mpr ts.le)) (show x'h∈N ℓt from hq'))⟩)
   let h_b:= (throughAll Y H V G C a χ F j z b Z p d v0 s A A' f0 f1 c Q' c₀ A0 p0 p1 qW o v B Pq ts tz s0 x'h hq' ((truthful ..).1 hx) t' 0); rw [ (Sq).eZero] at h_b; exact h_b
lemma awakeAt (s0:0≤ (s:ℝ))(x':G₀ j)(hx:x'∈FP) : L x'∈ FP:= (Submodule.mem_iInf (ΩX)).mpr (fun i=> wallSight Y H V G C a χ F j z b Z p d v0 s A A' f0 f1 c Q' c₀ A0 p0 p1 qW u v L eL i s0 x' hx) -- tune
end wall
end Boots
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget

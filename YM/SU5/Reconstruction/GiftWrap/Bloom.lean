import YM.SU5.Reconstruction.GiftWrap.Engaged
/-! # Wedge Reeh from large world (one direction,pair); still without Creased grants -/
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
local notation "Tm" i:max=> Picket.trans (S₀ i)
local notation "Ω" i:max=> Ω₀ i
local notation "Sq" => (S₀ j)
namespace Boots
local notation "lu" x:max=> (Tm j) ((x:ℝ) • basis z)
local notation "BC" => parcelUp Sq
open Quartz Quartz.Ship Quartz.Waltz Quartz.Bouy Sail Lens
local notation "M₀"=>floor Y H V G C a χ j univ
local notation "Ms"=>floor Y H V G C a χ j
local notation "Λ0" => parish M₀ (Ω j)
local notation "Vol" => owns_it M₀ (Ω j)
variable (h0 : owns_it (floor Y H V G C a χ j univ) (vocation Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))))
local notation "P'" => Ms (Wedge j z)
local notation "P''" => Ms (Counter j z)
local notation "J" => Flare Y H V G C a χ F j z b
local notation "Xx" => parish (Ms (Wedge j z)) (Ω j)
local notation "Xx'" => parish (Ms (Counter j z)) (Ω j)
local notation "Uq" => Picket.trans Sq
include F b h0
lemma strolled : owns_it P' (Ω j):= by
 apply extension Xx (Submodule.isClosed_topologicalClosure _) (Ω j) M₀ h0 (hub (Ω j) P'); -- exact operators by far-site spectators
 intro A h; refine clause Xx (Submodule.isClosed_topologicalClosure _) (Wing Y H V G C a χ j univ) (wing_star Y H V G C a χ F j univ) ?_ A h
 have u(t:E4): MapsTo (Uq t) Xx Xx:= by
    have C0: Picket.Paces z Sq:=  ((grants Y H V G j _ _ (le_refl (0:ℝ)) zero_lt_one (((real_boost_purchase Y H V G C a χ (le_refl (0:ℝ)) (show 0<(1:ℝ) from zero_lt_one)).2 F).purchases j)).2 z b.symm)
    exact stay_everywhere b.symm (S₀ j) P' (Ω j) (fun _=> compass_origin ..) (fun x h y δ=> translation_bound Y H V G C a χ F j (Wedge j z) _ y (by rintro _ ⟨i,h,rfl⟩; exact sun_plus h δ) x h) C0 t
 rintro _ ⟨U₁,W,t,A,h,_,rfl⟩
 obtain ⟨r,rh⟩:=Chambers.Schedule.very_late (a:=-(U₁ z:ℝ)) (daylight Tx)
 let g:=(r:ℝ) • basis z; let B:= BC g A
 have ht:B∈ P':= point_awake Y H V G C a χ F j z b B (⟨U₁+eject z r,W,B,(by rw [Pi.add_apply,eject_at,AddSubgroup.coe_add]; linarith),aheadSight Y H V G C a χ F j z b U₁ W r A h,Or.inl rfl⟩)
 rw [show A= BC (-g) B from (parcel_went ..).symm]; -- tune dependent B
 rw [← parcel_add]; exact fun i p=> u _ (loyal (Ω j) P' B ht (u _ p))
lemma otherFull : owns_it P'' (Ω j):= by
 have h(x:G₀ j):(J).f x ∈ Xx':=by
   let d:=strolled Y H V G C a χ F j z b h0; let L:=Xx'; let Y':= L.comap (J).f.toLinearMap
   have he:IsClosed (Y':Set (G₀ j)) := (show IsClosed (Xx':Set (G₀ j)) from Submodule.isClosed_topologicalClosure _).preimage (J).f.continuous
   apply Submodule.topologicalClosure_minimal _ _ he (d x); apply Submodule.span_le.mpr; rintro _ ⟨u,v,rfl⟩; change (J).f (u (Ω j))∈ Xx'
   have heq : Ω j=(J).f (Ω j):= (stillHere Y H V G C a χ F j z b).symm; rw[← (J).shade_light,← heq]
   exact transport_home P'' (Ω j) _ (reflection_bound Y H V G C a χ F j z b (Wedge j z) _ (by rintro _ ⟨i,e,rfl⟩; exact (BridgeClub.turning j z i).mpr e) _ v)
 intro x; rw[←(J).twice x]; exact h _
local notation "Wo" x:max=> curtains j z x
lemma myCurt (i:Bool): owns_it (Ms (Wo i)) (Ω j):= by cases i; exact otherFull Y H V G C a χ F j z b h0; exact strolled Y H V G C a χ F j z b h0 -- tune order
lemma costume (y:Bool)(t:E4): let T:= (fun x=>x+t) '' (curtains j z y); owns_it (floor Y H V G C a χ j T) (vocation Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))):= by
 intro t' x; let D0:= (Wo y); let I':= Ms (t'); let N : Submodule ℂ (G₀ j):=parish I' (Ω j); let d':= N.comap (Uq t).toLinearMap
 have h':IsClosed (d':Set (G₀ j)):= (show IsClosed (N:Set (G₀ j)) from Submodule.isClosed_topologicalClosure _).preimage (Uq t).continuous
 have ht: Uq (-t) x∈ d':= by
    apply Submodule.topologicalClosure_minimal _ _ h' (myCurt Y H V G C a χ F j z b h0 y _); apply Submodule.span_le.mpr; rintro _ ⟨u,e,rfl⟩; change Uq t (u (Ω j)) ∈ N; rw [← keepsLaw Y H V G C a χ j]; exact transport_home I' (Ω j) _ ((translation_cov Y H V G C a χ F j D0 t u).1 e)
 rw[← show Uq t (Uq (-t) x)=x from DFunLike.congr_fun (mail Sq t) x]; exact ht
-- and separating there by C x=star shift and translate, no Rank
lemma atCenter {y:Bool}{A:(G₀ j).Op}(d:A∈ Ms (Wo y))(t':A (Ω j)=0): A=0:= by
 apply Bouy.sees_ℓ _ (Ms (Wo (!y))) A _ t' (myCurt Y H V G C a χ F j z b h0 _)
 cases y
 · exact foes Y H V G C a χ F j z b d
 · exact spacelike Y H V G C a χ F j (Wedge j z) (Counter j z) (room_separated j z b) d
lemma offsetCenter {y:Bool}{x:E4}{A:(G₀ j).Op}(d:A∈ Ms ((fun i=>i+x) '' Wo y))(t:A (Ω j)=0): A=0:= by
 let A₀:= BC (-x) A; have ht:BC x A₀=A:= parcel_inv ..; have h:Picket.trans Sq (-x) ((vocation Y H V G.history G.clipped j false (C j) (w j)))=Ω j:=compass_origin .. -- `_`
 have h':A₀=0:= atCenter Y H V G C a χ F j z b h0 ((translation_cov Y H V G C a χ F j _ x A₀).2 (ht.symm ▸ d)) (show BC (-x) A (Ω j)=0 from (by rw [keepsLaw Y H V G C a χ j,t]; simp))
 rw [← ht,h']; unfold parcelUp; rw[mul_zero,zero_mul]
end Boots
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget

import YM.SU5.Reconstruction.Quartz.Pomona
import YM.SU5.Reconstruction.Quartz.Coup
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
local notation "Π" i:max=> opCarries Y H V G i (C i) (w i)
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
-- generic region macros currently on chosen pair only.More later.
variable (t:ℝ)(ω:Bool)
include p F
lemma march (r:Creased Y H V G C a χ F j z b) (x:(G₀ j).Op) : x∈ (Lvl j) (curtains j z ω) ↔ ascend t Z x∈ (Lvl j) (curtains j z ω):= by
 let h0:=transported_room Y H V G C a χ F j z b Z p r t 0 ω x; rw[eitherShift b.symm, show Picket.move j z t (0:E4)=0 from ?_] at h0; swap; · exact (show _ from (by unfold Picket.move Picket.rise Picket.lee Picket.rise;simp))
 simpa using h0
-- using once known joint rank. avoid needing a primitive rank on b's negative wedge
variable (r:Creased Y H V G C a χ F z j b.symm)
local notation "Mₒ"=> (Lvl z) (Wedge z j)
local notation "J"=> Flare Y H V G C a χ F z j b.symm
local notation "Tb"=> tug Z Z.look
local notation "Ω"=> Ω₀ z
local notation "ℒ"=> (Ship.join (M₁) (Pull Z.look M₂)) -- uses namespace (ship not opened?)
include r
lemma right_charge (x:(G₀ z).Op)(d:x∈ M₂) : (Tb).plume ((J).f (star x Ω))=(Tb).shadow (x Ω):= by
 let g:=back_quarter Y H V G C a χ F j z b Z p
 have hv: Z.Back.plume (x Ω)=Z.Back.shadow ((J).f (star x Ω)):= (engaged Y H V G C a χ F z j b.symm Z.Back g r).reverse x (foes Y H V G C a χ F z j b.symm d)
 rw[Clasp.shadow, Ship.tug_backside, Clasp.shadow,sub_sub_cancel]
 exact hv.symm
lemma right_ref(x:(G₀ z).Op)(d:x∈ M₂) : (J).shade x∈ (M₂).commutant:= by
 let g:=back_quarter Y H V G C a χ F j z b Z p; rw [←equalsShade Y H V G C a χ F z j b.symm Z.Back g r, VonNeumannAlgebra.commutant_commutant]; refine reflection_bound Y H V G C a χ F z j b.symm _ _ ?_ _ d; rintro _ ⟨y,h,rfl⟩;exact (BridgeClub.turn_fee z j y).mpr h
variable (s:Creased Y H V G C a χ F j z b)
include s
lemma congruent (e:owns_it (Ship.join (M₁) (Pull Z.look M₂)) (Ω₀ j)) : Pull Z.look M₂=M₁:=by
 let N:= ℒ; let φ:=Flare Y H V G C a χ F j z b;
 let Tj:=engaged Y H V G C a χ F j z b Z p s; let q:=back_quarter Y H V G C a χ F j z b Z p
 let g : N≤ M₁:= fun x h=> ((joining ..).1 h).1; have y: Pull Z.look.symm N≤ M₂:= fun x h=> (run_inv Z.look x) ▸ (((pulling ..).1 (((joining ..).1 ((pulling ..).1 h)).2))) -- tune
 have u(t:ℝ)(x:(G₀ j).Op)(p':x∈ N): ascend t Z x∈ N:=by
    rcases (joining ..).1 p' with ⟨u,e⟩; apply (joining ..).2; refine ⟨(march Y H V G C a χ F j z b Z p t true s _).1 u,(pulling ..).2 ?_⟩; rw [Ship.rearWave]; exact (march Y H V G C a χ F z j b.symm Z.Back q (-t) false r _).1 ((pulling ..).1 e)
 have h1:N=M₁:= Ship.absorbed Z _ N (Ω₀ j) φ g e p.vacuum.2 u Tj.charge Tj.reflect Tj.opp
 have h2: Pull Z.look.symm N= M₂:= by
    refine absorbed (Tb) M₂ _ Ω J y ?_ ?_ ?_ (right_charge Y H V G C a χ F j z b Z p r) (right_ref Y H V G C a χ F j z b Z p r) (stillHere Y H V G C a χ F z j b.symm)
    · rw [← p.vacuum.1]; exact awayRel Z.look N (Ω₀ j) e
    · intro t; rw[turnaside,q.vacuum.2]
    intro t x h; obtain ⟨x',e0⟩:= Z.look.conjStarAlgEquiv.surjective x; change (ι) x'=x at e0; subst x
    rw [go]; exact (Ship.both Z.look N _).1 (u t x' ((Ship.both Z.look N _).2 h))
 apply VonNeumannAlgebra.ext; intro x; rw[pulling,←h2]; exact Iff.trans (Ship.both Z.look N x).symm (by rw[h1])
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget

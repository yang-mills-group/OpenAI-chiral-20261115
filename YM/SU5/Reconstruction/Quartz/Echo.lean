import YM.SU5.Reconstruction.Quartz.HereThere
-- # Graph recipe on this same law through any authentic Quarter
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
include p F
lemma back_face : Brigade Y H V G C a χ z j b D₀ Z.Back:= by
 let k:=p.port; let T:= flank z 0∩ flank j 0; let P0:= Ds U; let B:= Ds T; let f:P0→ₗ[ℂ] B:= Submodule.inclusion (domain_mono Y H G (inter_comm _ _|>.subset)); let w': B→ₗ[ℂ]P0:=Submodule.inclusion (domain_mono Y H G (inter_comm _ _ |>.subset)); -- proof F unused except included
 let Dₘ:= lowland z 0 ∩ lowland j 0; let g: Ds Dₘ→ₗ[ℂ]Ds (lowland j 0∩lowland z 0):= Submodule.inclusion (domain_mono Y H G (Set.inter_comm _ _|>.subset))
 constructor
 · intro i; obtain ⟨x,e,v⟩:= k.sees (w' i); exact ⟨x,v,e⟩
 · intro x y; exact (k.meets (g x) y).symm
 · apply k.full.mono; rintro x ⟨i,t,v⟩; exact ⟨f i,v,t⟩
 intro M N e; suffices Z.Pass N M by intro i; obtain ⟨x,t,b⟩:=this i; exact ⟨x,b,t⟩
 apply k.pass N M; intro i; obtain ⟨x,t,v⟩:=e (f i); exact ⟨x,v,t⟩
lemma back_quarter : Quarter Y H V G C a χ z j b Z.Back:= by
 let R₀:= (Z.Back); let h:=back_face Y H V G C a χ F j z b Z p; let u:=onBeam Y H V G C a χ z j b Z.Back (F.present z) (F.present j) h; let d:=onStreet Y H V G C a χ z j b Z.Back (F.present z) (F.present j) h
 let A₀:= pencil z j b; let B₀:= pencil j z b.symm -- tune local where
 refine ⟨h,⟨u,d⟩, Picket.victory R₀ _ _ ?_ ?_,Picket.looksHeat b _ _ R₀ A₀ B₀ u,Picket.look_bill b _ _ R₀ A₀ B₀ u d,fun v=>⟨Picket.boost_pays ..,Picket.boost_bill b _ _ R₀ A₀ B₀ u d v⟩⟩
 · rw [← comesHome Y H V G C a χ z, ←comesHome Y H V G C a χ j]; exact h.sees (⟨1,domain_one ..⟩:Ds (flank z 0∩flank j 0))
 intro x; let T:=lowland z 0∩lowland j 0; have ht:= h.meets (⟨1,domain_one ..⟩ : Ds T) x
 rw[←backHome Y H V G C a χ z T (top_ready z j b),← backHome Y H V G C a χ j T (low_ready z j b)]; exact ht
where pencil(j z:Axis)(b:z≠j):Picket.Paces z (S₀ j):= (grants Y H V G j _ _ (le_refl (0:ℝ)) zero_lt_one (((real_boost_purchase Y H V G C a χ (le_refl (0:ℝ)) (show 0<(1:ℝ) from zero_lt_one)).2 F).purchases j)).2 z b -- `pencil` binder order tune
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget

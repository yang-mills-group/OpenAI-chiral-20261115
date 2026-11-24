import YM.SU5.Reconstruction.Crease.Monitor
import YM.SU5.Reconstruction.Crease.Turns
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
local notation "Φ"=> (Flare Y H V G C a χ F j z b).shade
local notation "Sx"=> S₀ j
open Picket
include F b
lemma heatStill (x:ℝ≥0): Φ ((Sx).E x)=(Sx).E x:= by
 let y(i:ℕ): ℝ≥0:=whenly (timeMesh Λ) i (⌊x/mill (timeMesh Λ) i⌋₊+1); let t(i:ℕ):= notch (timeMesh Λ) i ((⌊x/mill (timeMesh Λ) i⌋₊+1:ℕ):ℤ)
 have he(i:ℕ):(t i:ℝ)=(y i:ℝ):= natural_time ..
 let U:= Flare Y H V G C a χ F j z b; let hp : Tendsto y atTop (𝓝 x):= MeshClock.shade (timeMesh Λ) x
 have h(i):Φ ((Sx).E (y i))=(Sx).E (y i):=by
    have ht:= shifter Y H V G C a χ F j z b (eject j (t i)) (by simp only [coordinates_eject,eject_at, he]; positivity);
    rw [reverseAway z j b, bridge_time,he,Real.toNNReal_coe] at ht; exact ht
 ext1 v; rw [Flash.shade_at]; apply tendsto_nhds_unique_of_eventuallyEq (((U.f.continuous.tendsto _).comp (((Sx).continuousE (U.f v) |>.tendsto _))).comp hp) ((((Sx).continuousE v).tendsto _).comp hp); exact Eventually.of_forall fun i=> DFunLike.congr_fun (h i) v
local notation "ℱ"=>Picket.trans (S₀ j)
lemma silverStamp (m:Axis)(q:m≠j)(t:Gt): Φ (ℱ ((t:ℝ) • basis m))=ℱ ((if m=z then -(t:ℝ) else (t:ℝ)) • basis m) := by
 have he:= shifter Y H V G C a χ F j z b (eject m t) (by simp [q.symm]); rw [castSpace Y H V G C a χ j q] at he
 split_ifs with ht
 · subst z; rw [reverse_eject,castSpace Y H V G C a χ j q] at he; exact he
 rw [reverseAway z m ht,castSpace Y H V G C a χ j q] at he; exact he
open YM.BridgeClub
lemma orbitF (x:E4): Φ (ℱ x)= ℱ (turn j z x):=by
 have he(m:Axis)(x:ℝ):Φ (ℱ (x • basis m))= ℱ (turn j z (x • basis m)):=by
   rw [turn_ray]; by_cases h:m=j
   · rw [if_pos (Or.inl h),h]; exact Flash.timeback _ _ (heatStill Y H V G C a χ F j z b) x
   ext1 v; let A:= Flare Y H V G C a χ F j z b; let kT(t:ℝ):= if m=z then -t else t -- notation shadows! rename
   rw [show (if m=j ∨ m=z then -x else x)=kT x by simp [kT,h]]
   obtain ⟨k0,p,l⟩:= mem_closure_iff_seq_limit.mp (daylight (timeMesh Λ) x); let k'(i):↥(marks (timeMesh Λ)):= ⟨k0 i,p i⟩; have hn: Continuous kT:= by unfold kT; split_ifs <;> fun_prop
   rw [Flash.shade_at]; apply tendsto_nhds_unique_of_eventuallyEq ((A.f.continuous.tendsto _).comp ((((Sx).unit.moves (A.f v)).tendsto _).comp (l.smul tendsto_const_nhds))) ((((Sx).unit.moves v).tendsto _).comp (((hn.tendsto _).comp l).smul tendsto_const_nhds)); exact Eventually.of_forall fun i=> DFunLike.congr_fun (silverStamp Y H V G C _ _ F j z b m h (k' i)) v
 have ht(x:E4):∑ i: Axis,x i • basis i=x:=by ext1 i;simp
 suffices ∀ s:Finset Axis,let u:=∑ i ∈ s,x i • basis i; Φ (ℱ u)=ℱ (turn j z u) by simpa [ht] using this Finset.univ
 intro s; dsimp only; induction s using Finset.induction_on with
 | empty=>
   simp only [Finset.sum_empty, turn_zero,Picket.trans, Spectral.Orbit.origin]; ext1 v; exact (Flare Y H V G C a χ F j z b).twice v
 | insert i s d ih=> rw [Finset.sum_insert d,turn_add,trans_sum,trans_sum,Flash.shade_mul, he,ih]
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget

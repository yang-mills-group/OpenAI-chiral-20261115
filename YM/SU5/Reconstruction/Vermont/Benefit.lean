import YM.SU5.Reconstruction.Vermont.Rime
set_option autoImplicit false
set_option maxHeartbeats 800000
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
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "m₁" => FirstWindows.move (tent Y H)
local notation "ℓ_"=>osValue Y H V G a (C a) χ
open BridgeClub Reflector
namespace Crease
variable (F: BoostBacking Y H V G C a χ)
variable (j z:Axis) (b:j≠z)
open Lens Sail
local notation "Π₀" i:max=> opCarries Y H V G i (C i) (w i)
local notation "L0" => Sight Y H V G C a χ j
local notation "Fz" => (Vo z)
local notation "ζ"=> floor Y H V G C a χ j
local notation "S"=> (S₀ j)
-- Receipt: scripts called in localized spacetime region, all paying equal duration (Length fixed).
-- Norm budget uniform; check only weak vacuum ket; don't also check *star* (measures other border).
structure Optical (Q': Set E4) (t:marks (timeMesh Λ)) (B:(G₀ j).Op)(M:ℕ→(G₀ j).Op) : Prop where
  armour : ∃ c, ∀ n, Script (S₀ j) (ζ Q') (M n) (Real.toNNReal (t:ℝ)) c
  fare (p:G₀ j): Tendsto (fun n=> inner ℂ p (M n (Ω₀ j))) atTop (𝓝 (inner ℂ p (B (Ω₀ j))))

open TopologicalSpace
lemma portrait : SeparableSpace ((G₀ j):Type):=by
 letI : SeparableSpace ((J₀ j):Type):= Hearthbank.separable Y H V G j (C j) (w j)
 change SeparableSpace ((C₀ j):Type) -- defeq?
 exact inferInstance

include b F
open Schedule
lemma charged (k:Creased Y H V G C a χ F j z b) (U:Set E4)(R:ℝ) (v:∀ x∈ U, |x j|+x z≤ R) (t:Gt)(p:0≤ (t:ℝ))
    (A:(J₀ j).Op)(x: Sky K)(u:(Q j) x t A) (M:ℕ→ (G₀ j).Op)
    (h:Optical Y H V G C a χ j U t ((Π₀ j) A) M) : Limited atTop M ((Π₀ j) A):= by
 let B:=(Π₀ j) A; let Ω:= (Ω₀ j);
 obtain ⟨A₀,ka,hA,kk⟩:= (compact_domain Y H G).1 u.pose; obtain ⟨d,d',p1,t1⟩:= shutters (daylight (timeMesh Λ)) z ka
 let f:= d'-d; have hf : 0<(f:ℝ):= (show (0:Gt)< f from sub_pos.mpr p1)
 let hp : m₁ (eject z (-d)) x ∈ D (Chambers.strip z 0 (f:ℝ)) := by
   apply domain_mono Y H G _ (moving Y H V G _ _ kk); rintro _ ⟨y,g,rfl⟩
   simp only [slides,Chambers.strip,mem_setOf_eq,Pi.add_apply,coordinates_eject, eject_at, AddSubgroup.coe_neg]
   unfold f; simp only [Icc, AddSubgroup.coe_sub]; obtain ⟨e,w1⟩:= t1 y g; constructor<;> linarith
 obtain ⟨A',k0⟩:= fits Y H V G z (C z) (w z) f hf _ hp
 obtain ⟨t',u0⟩:= very_late (a:=(t:ℝ)) (daylight (timeMesh Λ))
 obtain ⟨c,e0⟩:= h.armour; letI:= portrait Y H V G C a χ j
 have pay (n:ℕ): ‖M n‖ ≤(c:ℝ):= (e0 n).pays
 refine ⟨⟨_,(c:ℝ≥0).property,Eventually.of_forall pay⟩,fun x y=>?_⟩
 apply tendsto_of_subseq_tendsto; intro ns hns; obtain ⟨ψ,a0,b0,e,u₁⟩:= Limited.extract (M∘ns) c.property (fun i=> pay (ns i))
 have h1: b0 Ω=((Π₀ j) A) Ω:= by
   apply ext_inner_left ℂ; intro z; exact tendsto_nhds_unique (u₁.confirms z Ω) ((h.fare z).comp (hns.comp a0.tendsto_atTop))
 refine ⟨ψ,(by
    rw [show opCarries Y H V G j (C j) (w j) A=b0 from (ascertain Y H V G C a χ F j z b d f A A' t t' u k0 U R b0 h1 c (fun n=>e0 (ns (ψ n))) u₁ v u0 p k).symm]; exact u₁.confirms ..)⟩ -- `rw` goal may defeq
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget

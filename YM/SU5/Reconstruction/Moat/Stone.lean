import YM.SU5.Reconstruction.Moat.Economy
import YM.SU5.Reconstruction.Moat.Pulse
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
namespace Reflector
variable (j:Axis)
local notation "Π₁"=> opCarries Y H V G j (C j) (w j)
local notation "Ω" i:max=>doorstep Y H V G.history G.clipped i false (C i) (w i)
open Roy
open Moat
variable (P : BoostBacking Y H V G C a χ)
variable (r:ℕ→marks (timeMesh Λ))(A:ℕ→Sky (tent Y H))
-- polys with bounded norm in all registers (see economy) used on ANY programs. For limit additionally asks uniform OP.
variable {M:ℝ}(v:∀ i, Licensed Y H V G C a χ (A i) (r i) M)
variable (T:ℕ→(indoor Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op)
  (p:∀ i, Follows Y H V G j (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j)) (A i) (r i) (T i))
  (h:∀ i,0<(r i:ℝ)) (hs:Tendsto (fun i=>(r i:ℝ)) atTop (𝓝 0))
local notation "Pv" u:max v:max=> (S₀ j).ℚmeasure.region (Moat.band j u v)
include P v hs h p
lemma drifting (u v':ℝ)(he:0<u)(v0:0≤v') : Tendsto (fun i=>(Pv u v') (Π₁ (T i) (Ω₀ j))) atTop (𝓝 0) ∧ Tendsto (fun i=>(Pv u v') (Π₁ (star (T i)) (Ω₀ j))) atTop (𝓝 0):=by
 simp_rw [(carries Y H V G C a χ j _ _ (p _) (P.present j) (h _)).1,(carries Y H V G C a χ j _ _ (p _) (P.present j) (h _)).2]
 let D1(i):=(Vo j) (outgoing Y H G j (A i) (r i) (p i|>.pose)); let D2(i):=(Vo j) (returning Y H V G j (A i) (r i) (p i|>.pose))
 have s₀(ε:ℝ)(he':0<ε):∀ᶠ i in atTop, ‖(Pv u v') (D1 i)‖ < ε ∧ ‖(Pv u v') (D2 i)‖ < ε :=by
       obtain ⟨z,k,g⟩:= economy Y H V G C a χ P.present P.forward j M u v' ε he v0 he'
       filter_upwards [hs.eventually (ge_mem_nhds k)] with i hi
       have hB : ‖(Pv u v') (D1 i)‖^2 + ‖(Pv u v') (D2 i)‖^2 < ε^2:= g (r i) (h i).le hi _ (v i)
       constructor <;> nlinarith [sq_nonneg (‖(Pv u v') (D1 i)‖),sq_nonneg (‖(Pv u v') (D2 i)‖)] -- and via constructor
 rw [Metric.tendsto_nhds, Metric.tendsto_nhds]; constructor
 · intro ε e; filter_upwards [s₀ ε e] with i hi; rw [dist_zero_right]; exact hi.1
 intro ε e; filter_upwards [s₀ ε e] with i hi; rw [dist_zero_right]; exact hi.2

omit P v p h hs
private lemma flipped_limit {H:Hilbert}{B:H.Op}{C:ℕ→H.Op}(p:Limited atTop C B) : Limited atTop (fun i=> star (C i)) (star B):= by
 refine ⟨?_,fun x y=>?_⟩
 · simpa using p.uniform
 simp_rw [_root_.ContinuousLinearMap.star_eq_adjoint, _root_.ContinuousLinearMap.adjoint_inner_right]; -- names
 have z: ∀ x y:H,inner ℂ x y= (starRingEnd ℂ) (inner ℂ y x):=fun _ _=>(inner_conj_symm _ _).symm
 conv => arg 1; ext i; rw [z]
 rw [z (B _)]; exact (p.confirms y x).star
include P v p h hs
variable {B:(indoor Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op} (Hh:Limited atTop T B) (C₁ : FullWins Y H V G C a χ)
include C₁ Hh
lemma resolution : (star B) (Ω j) = inner ℂ (Ω j) ((star B) (Ω j)) • (Ω j):=by
 let s:=(Pv 0 0) -- local
 have hz: cue (S₀ j) (Π₁ (star B) (Ω₀ j))=Π₁ (star B) (Ω₀ j):= low_limit (S₀ j) atTop (Hearthbank.projected Y H V G j (C j) (w j) (flipped_limit Hh)) (Ω₀ j) (fun u w' p0 h0=>(drifting Y H V G C a χ j P r A v T p h hs u w' p0 h0).2)
 let p:= P.present j
 have he : Π₁ (star B) (Ω₀ j)= inner ℂ (Ω₀ j) (Π₁ (star B) (Ω₀ j)) • (Ω₀ j) := hz.symm.trans ((little_due Y H V G C a χ C₁ (r:=0) le_rfl (fewer Y H V G C a χ le_rfl P)).2.unique_normal j _)
 rw [Hearthbank.uplink] at he
 have h:=congrArg (fun x:G₀ j=>(x.val:J₀ j)) he; change ((Π₁ (star B) (Ω₀ j):G₀ j).val:J₀ j)= _ • ((Ω₀ j).val:J₀ j) at h; rwa [carries_full Y H V G j (C j) (w j) p, vocate] at h
end Reflector
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget

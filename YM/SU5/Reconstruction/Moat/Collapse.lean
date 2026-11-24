import YM.SU5.Reconstruction.Moat.Stone
import YM.SU5.Reconstruction.Moat.Spill
import YM.SU5.Reconstruction.Cashier.AtMint
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
-- Pack. want also finite packing receipt explicitly.END.
variable (j:Axis)(x:ℕ→ Sky (tent Y H))(t:ℕ→marks (timeMesh Λ))
variable (P:BoostBacking Y H V G C a χ)(p:FullWins Y H V G C a χ)
local notation "Ω" i:max=> doorstep Y H V G.history G.clipped i false (C i) (w i)
-- no automatic ability to compare program or Λ.Time outputs if occupations high.need Pace.Spaces occupied, not assume Fill.
structure Duplex (M:ℝ) :Prop where
  heels : ∀ i, 0<(t i:ℝ)
  shrimp : Tendsto (fun i=>(t i:ℝ)) atTop (𝓝 0)
  arrives (i:ℕ) (j:Axis) : ∃ A:(indoor Y H V G.history G.clipped j false (C j) (w j)).Op, Follows Y H V G j (C j) (w j) (x i) (t i) A ∧ ‖A‖≤ M
variable {M:ℝ}(e:Duplex Y H V G C a χ x t M) {B:(indoor Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op}
variable (L:ℕ→(indoor Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op) (u:∀ i,Follows Y H V G j (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j)) (x i) (t i) (L i)) (k':Limited atTop L B)
include e
lemma allPro (i:ℕ): Licensed Y H V G C a χ (x i) (t i) M:= fun j=> billed Y H V G C a χ j _ _ (e.arrives i j).choose_spec.1 (e.heels i) (e.arrives i j).choose_spec.2
-- Buying Back: all such limits at this appointment are certainly SCALAR. Not using any continuum star extension hypothesis. 
include P p u k'
lemma glassFate : ∃ k:ℂ,B=k • (1:(indoor Y H V G.history G.clipped j false (C j) (w j)).Op):= by
 obtain ⟨b,d⟩:= exists_ne j
 haveI sd: TopologicalSpace.SeparableSpace (J₀ b).space:= Hearthbank.separable Y H V G b (C b) (w b)
 choose A tA hA using fun i=> e.arrives i b
 let κ (i:ℕ):= allPro Y H V G C a χ x t e i
 have hM:0≤M:=(norm_nonneg _).trans (hA 0); obtain ⟨ψ,Q0,K',v,g⟩:= Limited.extract A hM hA; let tU:= Q0.tendsto_atTop
 have hT: (star K') (Ω b) = inner ℂ (Ω b) ((star K') (Ω b)) • (Ω b) := resolution Y H V G C a χ b P (t∘ψ) (x∘ψ) (fun i=>κ (ψ i)) _ (fun i=> tA (ψ i)) (fun i=> e.heels (ψ i)) (e.shrimp.comp tU) g p -- T inferred
 let R:= notch (timeMesh Λ) 0 1; have hx:0< (R:ℝ):=by change 0< bell Tx 0 1; unfold bell; simpa using mill_pos (timeMesh Λ) 0
 have h':Limited atTop (L∘ψ) B:=by obtain ⟨X₀,V0,d⟩:= k'.uniform; exact ⟨⟨_,V0,tU.eventually d⟩,fun x y=> (k'.confirms x y).comp tU⟩
 exact ⟨star (inner ℂ (Ω b) ((star K') (Ω b))), coercive Y H V G C a χ j b d R P (L∘ψ) (A∘ψ) (x∘ψ) (t∘ψ) (e.shrimp.comp tU) (fun i=>u (ψ i)) (fun i=> tA (ψ i)) h' g hT hx⟩
omit e u k' P p
open Hearthbank SlabMark.Bankroll
-- Deco $w` is width. Dense.St.
variable (q w' d n:ℕ) (h:0<w')(ℓ:SU.Slot)
-- er use notch argument.w'. lit
local notation "Θ" i:max=> notch (timeMesh Λ) i w'
lemma livewidth (u:ℕ) (w':ℕ)(p:0<w'): 0< (notch (timeMesh Λ) u w':ℝ):= by
 rw [show (notch (timeMesh Λ) u w':ℝ)=(whenly (timeMesh Λ) u w':ℝ) from natural_time ..]; exact when_pos _ u w' p
lemma sponsor {f g: SU.Slot → observable (tent Y H) true} {z:ℝ}{i n' :ℕ} (r: Deliver Y H V i G w' C d q n f g z n') : ∃ A:(indoor Y H V G.history G.clipped j false (C j) (w j)).Op,Follows Y H V G j (C j) (w j) (toSkybox Y H G i (g ℓ)) (Θ i) A∧ ‖A‖≤ 2:= by
 obtain ⟨A,h,h₁⟩:= chooseLive Y H V G a C χ j ℓ r; exact ⟨A,h, harvest_price Y H V G a C χ j _ h₁⟩
include h P
local notation "T'"=> (Moat.band j)
-- any scale trajectory all late resolution CP9 budgets in particular disappear on actual appointed if Back
lemma wanted (u v ρ:ℝ)(he:0<u)(p:0≤v)(s:0<ρ): ∀ᶠ i in atTop,∀ e:ℕ,∀ (f g:SU.Slot→ observable (tent Y H) true)(z:ℝ) (r:Deliver Y H V i G w' C d q n f g z e),
    let x:= sponsor Y H V G C a χ j q w' d n ℓ r; let a':= (S₀ j).ℚmeasure.region (Moat.band j u v)
    let Φ:= toSkybox Y H G i (g ℓ)
    ‖a' ((Vo j) (outgoing Y H G j Φ (Θ i) x.choose_spec.1.pose))‖^2 + ‖a' ((Vo j) (returning Y H V G j Φ (Θ i) x.choose_spec.1.pose))‖^2 < ρ^2:= by
 obtain ⟨u',l,w0⟩:= economy Y H V G C a χ P.present P.forward j 2 u v ρ he p s
 have e : Tendsto (fun i:ℕ=> ((Θ i):ℝ)) atTop (𝓝 0):= by simp_rw [show ∀ i:ℕ,(notch (timeMesh Λ) i w':ℝ)=(whenly (timeMesh Λ) i w':ℝ) from fun _=>natural_time ..]; exact NNReal.tendsto_coe.mpr (skinny (Λ:=Λ) w')
 filter_upwards [e.eventually (ge_mem_nhds l)] with i p; intro z f g u vi x a' Φ; have h₀:=livewidth (Λ:=Λ) i w' h; refine w0 (Θ i) h₀.le p Φ (fun i' =>?_); let h:= sponsor Y H V G C a χ i' _ _ _ _ ℓ vi; exact billed Y H V G C a χ i' _ _ h.choose_spec.1 h₀ h.choose_spec.2
include P p h
lemma resin (B:(indoor Y H V G.history G.clipped j false (C j) (w j)).Op)(L:Embers Y H V G a C χ j ℓ n w' q d B) : ∃ k:ℂ,B=k • (1:(indoor Y H V G.history G.clipped j false (C j) (w j)).Op):= by
 obtain ⟨ψ,y,f,f',ζ,A,Hψ,v,v',z,u⟩:= L.price
 let F(i:ℕ):=toSkybox Y H G (ψ i) (f' i ℓ); let t(i:ℕ):= Θ (ψ i); have hT:Tendsto (fun i:ℕ => (notch (timeMesh Λ) i w':ℝ)) atTop (𝓝 0):= by simp_rw [show ∀ i:ℕ,(notch (timeMesh Λ) i w':ℝ)=(whenly (timeMesh Λ) i w':ℝ) from fun _=>natural_time ..]; exact NNReal.tendsto_coe.mpr (skinny (Λ:=Λ) w')
 exact glassFate Y H V G C a χ j F t P p (M:=2) ⟨fun i=>livewidth (ψ i) w' h, hT.comp Hψ.tendsto_atTop,fun i j'=> sponsor Y H V G C a χ j' _ _ _ _ ℓ (v' i)⟩ A (fun i=>(z i).1) u
end Reflector
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget

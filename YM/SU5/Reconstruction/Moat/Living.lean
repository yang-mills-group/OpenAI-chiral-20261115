import YM.SU5.Reconstruction.Moat.Collapse
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
variable (u y q d:ℕ) (v:0<y)(p:FullWins Y H V G C a χ)
open Hearthbank SlabMark.Bankroll
local notation "Θ" i:max=> notch (timeMesh Λ) i y
/-- Spacetime plate rigidity consequence. Uses arbitrary (not necessarily pointlike costly Star-fields). Schedule exactly from selection. Need Forward receipt. -/
structure Resheet : Prop where
  forward_limit (P:BoostBacking Y H V G C a χ)(j:Axis)(v u ε M:ℝ)(hu:0<u)(hv:0≤v)(e:0<ε) : ∃ h> (0:ℝ),∀ (t:marks (timeMesh Λ)),0≤ (t:ℝ)→(t:ℝ) ≤ h→∀ (p:Sky (tent Y H)) (q: Licensed Y H V G C a χ p t M),
     let Z:= (S₀ j).ℚmeasure.region (Moat.band j u v)
     ‖Z ((Vo j) (outgoing Y H G j p t (q j).registers))‖^2+‖Z ((Vo j) (returning Y H V G j p t (q j).registers))‖^2< ε^2
  scalar (P:BoostBacking Y H V G C a χ)(j:Axis)(x:ℕ→Sky (tent Y H))(t:ℕ→marks (timeMesh Λ))(M:ℝ)(Y₁: Duplex Y H V G C a χ x t M)
    (T:ℕ→(indoor Y H V G.history G.clipped j false (C j) (w j)).Op) (r:∀ i,Follows Y H V G j (C j) (w j) (x i) (t i) (T i)) (B:(indoor Y H V G.history G.clipped j false (C j) (w j)).Op)(h:Limited atTop T B) : ∃ k:ℂ,B=k • (1:(J₀ j).Op)
  drift (P:BoostBacking Y H V G C a χ) (j:Axis)(ℓ:SU.Slot)(b c ρ:ℝ)(p:0<b)(h:0≤ c)(t:0<ρ): ∀ᶠ i in atTop,∀ e:ℕ,∀ (f g:SU.Slot→ observable (tent Y H) true)(z:ℝ) (r:Deliver Y H V i G y C d q u f g z e),
    let x:= sponsor Y H V G C a χ j q y d u ℓ r; let a':= (S₀ j).ℚmeasure.region (Moat.band j b c)
    let Φ:= toSkybox Y H G i (g ℓ)
    ‖a' ((Vo j) (outgoing Y H G j Φ (Θ i) x.choose_spec.1.pose))‖^2 + ‖a' ((Vo j) (returning Y H V G j Φ (Θ i) x.choose_spec.1.pose))‖^2 < ρ^2
  petro (P:BoostBacking Y H V G C a χ)(j:Axis)(z:SU.Slot)(B:(indoor Y H V G.history G.clipped j false (C j) (w j)).Op)(e: Embers Y H V G a C χ j z u y q d B) : ∃ k:ℂ,B=k • (1:(indoor Y H V G.history G.clipped j false (C j) (w j)).Op)
include p v
lemma price_more : Resheet Y H V G C a χ u y q d:=by
 constructor
 · intro P j tr u ε M hu hv e; exact economy Y H V G C a χ P.present P.forward j M u tr ε hu hv e
 · intro P j x t M H' T h B e; exact glassFate Y H V G C a χ j x t P p H' T h e
 · intro P j l b c ρ p₀ h e; exact wanted Y H V G C a χ j P q y d u v l b c ρ p₀ h e
 intro P j z B e; exact resin Y H V G C a χ j P p q y d u v z B e
end Reflector
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget.Reflector.price_more

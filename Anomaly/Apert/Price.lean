import Anomaly.Apert.Fleet
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip Pastry Hake Peaks Fock Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Rive Ione Larch Roots Push.AbsoluteSums.Trees Sour Py Mew PowerSeries
open scoped Mew
open Neon Moto Taxi Bake QuadClock
variable {N B:Side}
local notation "Ω"=> mid N B
variable {P:GramM (mid N B)}{g h d q a μ:ℝ}{n l k m:ℕ}{I:Type}[Fintype I][LinearOrder I]
    (K: Key I→ Rinse (Seat (mid N B)) (Copy (mid N B))) (C:Occlus P.p)
    (σ:I→Site (mid N B))
    {M:Key I→ Orbit (mid N B)→ Aura (mid N B)→ FC (Dwell (mid N B))}
    {y b: Aura (mid N B)→ℝ}{r:Aura (mid N B)→Support (More (mid N B))→ℝ}
    (X:OrbitRack C (Cube.node∘σ) n P.K h K y b r M)
local notation "O"=> Cube.node∘σ
variable (τ: Ids (mid N B))(Q: I→ RegBudget (mid N B))(c:I→ ArcΦ)(Fv:I→Cusp (mid N B))(t:I→ℂ)
local notation "Tμ"=> lensG (P:=P.p) P.K K k
local notation "Tp"=> lensSimple P.K K k
local notation "Ψf" => mkCup P.p P.K K k Fv
local notation "QΨ"=> bustle (O) Ψf
variable (Z:∀ i:I,Ice l (σ i) P.p h q d a (coldE P.p (τι (lensG (P:=P.p) P.K K k) [i])) (Q i) (Fv i) (t i) (c i))
local notation "Lχ" => awake (O) (lensD (P:=P.p) P.K K k τ) Q

variable (hp:1≤h)
include X Z hp
lemma pulseStencil : Notice σ Lχ QΨ ∧ (∀ i,νTip Lχ i=Q i∧ emberTip QΨ i= emberTip Ψf i) := by
  let g:= sealE (R:=P) C K O n M X k hp τ
  let f:= flows_cup K C σ X k Fv hp (fun i=>(Z i).stout)
  have L(i):νTip Lχ i=Q i := value_E ..
  have V(i):emberTip QΨ i=νΦK Ψf {i}:= value_F ..
  refine ⟨⟨cash0 ..,fun x=>?_,eReady O Q (lensD (P:=P.p) P.K K k τ),fun i=>quietF O Ψf f i, fReady O Ψf,fun i w=>by rw [L i,V i]; exact ⟨crest_E ..,crest_K ..⟩ ⟩,fun i=>⟨L i,(V i).trans (funext₂ fun x y=> Py.cue_1 _ _)⟩⟩
  exact quietE (O) Q (lensD (P:=P.p) P.K K k τ) g (fun i X h=> show node (σ i) ∈ X.val.2 from (not_not.mp fun t=> h ((Z i).axle.site X t)) ▸ X.property) x

variable {L:Side}{W':ℝ}
lemma chargedSleeve (hl:l=L.val)(pD:0 ≤ d)(u:GapN σ P.p.B l m) (pE:3*C.η ≤ 2) (uQ:(m:ℝ)*d+ C.γ*(1-degreePrice P.p.B C.γ C.η)⁻¹≤1)
    (hK:C.γ + Real.exp 1*(C.γ*(1-degreePrice P.p.B C.γ C.η)⁻¹ + m*d) ≤100*C.γ)
    (F:Force_M P.p.B (Cube.node∘σ) m) (hs:27*(m:ℝ) ≤ C.η*(P.p.B:ℝ)^2)
    (hq:0≤q) (i:Key I) (w:∀ j,‖i j‖≤2) : IncX primeU (Lχ i) P.p h (2*q*m+ sigma (C.η+C.η) P.p.B*yσE P.p C) ∧ Dark primeU (QΨ i) P.p h (Real.exp (3*(m:ℝ))*yσF P.p C):=by
  have e:4 ≤ Real.exp 3:= le_trans (by norm_num) (Real.add_one_le_exp 3)
  let p:=fun i=>(Z i).axle
  have L₂(i): Axon L.val (σ i) P.p (Q i) h q (c i):=hl ▸ p i
  let V:=flows_cup K C σ X k Fv hp (fun i=>(Z i).stout)
  choose q' U f S using fun i=> (Z i).grant
  have h (i hi):=glowMoney K C σ X k Fv q' U S f hp pD u pE uQ hK i hi
  refine ⟨add_v _ _ _ (lean_C P σ m hp L Q c F L₂ i w hq) (many_e C K O n M X k hp τ i w 3 e (by norm_num) ?_ F),?_⟩ -- tune
  · rw [show (9:ℝ)*3=27 by norm_num]; exact hs
  refine forceBudget (O) F _ V i 2 w _ 3 one_le_two (by nlinarith only [e]) (by norm_num) C.hη.le (zero_lt_one.trans_le hp) _ (fun i t=>(h i t).1) (h 0 roots).2 ?_ -- tune Γ
  nlinarith only [hs, Nat.cast_nonneg (α:=ℝ) m]
end YM.CF.Vow.TreasuryFog

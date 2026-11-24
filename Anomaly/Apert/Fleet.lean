import YM.SU5.Exchange.Seed.Pip
import YM.CF.Neon.Plast
import SatinThinTopic
set_option maxHeartbeats 500000
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip
open Pastry Hake Peaks Fock Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Rive Ione Larch Roots Push.AbsoluteSums.Trees Sour Py Push.AbsoluteSums Mew PowerSeries
open scoped Mew
open Neon Moto Taxi Bake QuadClock
variable {n N B:Side}
local notation "Ω" => mid N B
local notation "Θ"=> Cue
variable {q L m:ℕ}{p:BudgetPoint}{F:ForceBudget (mid N B)}{d h g:ℝ}{I:Type}[LinearOrder I][Fintype I]
    (K: Key I→ Rinse (Seat (mid N B)) (Copy (mid N B)))
    (C: Occlus p)
    (σ:I→ Site (mid N B)) {M:Key I→ Orbit (mid N B)→ Aura (mid N B)→ FC (Dwell (mid N B))}
    {a b: Aura (mid N B)→ℝ}{r:Aura (mid N B)→Support (More (mid N B))→ℝ}
    (X:OrbitRack C (Cube.node∘σ) q F h K a b r M)

variable (u:ℕ)(Fv: I→Cusp (mid N B))
local notation "o"=> p.supportExponent
local notation "η"=> C.η
local notation "σℓ"=> p.supportExponent+C.η+C.η
local notation "s"=>p.supportExponent+C.η+C.η+C.η
local notation "α"=> C.γ
local notation "t"=> paidLayers r a b u

local notation "Ψg"=>lensG (P:=p) F K u
local notation "Θw"=>lensCells F K u
local notation "Θh"=>lensSimple F K u
local notation "Z"=>Φstack Fv
abbrev mkCup (P:BudgetPoint) (F:ForceBudget (mid N B)) (i: Key I→ Cadre.Rinse (Seat (mid N B)) (Copy (mid N B))) (u:ℕ) (X:I→ Vow.Cusp (mid N B))(z:Mew.Key I):ForceBudget (mid N B):=budgetR (roomV P (lensSimple F i u z) (lensCells F i u z) (Φstack X z))
local notation "W"=> mkCup p F K u Fv

variable (l:Vow.Cusp (mid N B)→Prop) -- unused
include X
lemma budget_genesis (v:1≤h) : mkCup p F K u Fv 0=budgetR (settleK F) := by
  let G:= lensOrigin C F K (Cube.node∘σ) q M X u v (Classical.arbitrary (Ids Ω)); rw [mkCup,Φstack, sum_eq_zero (fun i _=> ?_)]; exact G.2; change (0:ℂ) • _=0; rw [zero_smul]
lemma flows_cup (v:1≤h) (pX:∀ i,∀ x:Aura (mid N B), node (σ i)∉x.val → Fv i x=0) :∀ x:Force (mid N B),Hush (Cube.node∘σ) x.val.1.val.2 (fun z:Key I=> W z x) ∧ ∀ V:Orbit Ω,River (fun z=> W z x V):=by
  obtain ⟨G,U⟩:=ωF_H σ Fv pX
  intro x; refine ⟨?_,?_⟩
  · intro z hv g w b; apply congrArg (bassH (lordD x) • ·); exact moto_H (W0:=Θw) (P:=p) (L0:=Z) (Cube.node∘σ) (X.turns u) (G) (lordD x) x.val.2 z hv g w b -- p shadow
  intro U'; let e:=lordD x; change River (fun z:Key I=> bassH e • (roomV p (Θh z) (Θw z) (Z z) e x.val.2 U')); refine bScale _ (moto_R (P:=p) Θw Z (layerRay C F K (Cube.node∘σ) q M X u v) U (lensSimpleR C F K (Cube.node∘σ) q M X u v) _ _ U') _ -- tune

-- Root sum test uniform for Θ-stack. stack prices on common bill, not independent coefficients.
variable (μ: I→ Aura (mid N B)→ℝ)(D:ℝ)
    (A:∀ i,Anuk (Fv i) (μ i) p h)
    (S:∀ i, SparF (σ i) p (μ i) L)
    (V:∀ i,∀ x: Seat (mid N B),tallB (μ i) p.B (p.supportExponent+1+1) x ≤ d)
local notation "Aμ" => (∑ i:I, μ i)
include A S V
lemma prepares (pD:0 ≤ d)(v:1≤h)(pK:GapN σ p.B L m) :∀ z∈ hill I, Anuk (Z z) Aμ p h ∧∀ y: Seat Ω,tallB Aμ p.B (p.supportExponent+1+1) y ≤ m*d:=by
  let Y:Mew.Key I:=1
  let E:=moon_Z p h L σ Fv (fun _=>d) μ A S V m pK Y d pD fun i=> by change ‖(1:ℂ)‖* _≤_; simp -- ABI
  intro z q; constructor; swap; · simpa only [Y,Pi.one_apply,norm_one, one_smul] using E.2
  let Pt:=moon_Z p h L σ Fv (fun _=>d) μ A S V m pK z d pD (fun i=>mul_le_of_le_one_left pD ((norm_le_pi_norm ..).trans (mem_closedBall_zero_iff.mp q)))
  refine ⟨?_,?_⟩; · exact Finset.sum_nonneg fun i _=> (A i).1
  intro i F H u; apply (Pt.1.2 i F H u).big; rw [Finset.sum_apply,Finset.sum_apply]; refine sum_le_sum ?_; intro x _; exact mul_le_of_le_one_left ((A x).1 _) ((norm_le_pi_norm ..).trans (mem_closedBall_zero_iff.mp q))

-- additional Glow money on same gamma. reserve.F
variable (v:1≤h)(pD:0≤d)(gA:GapN σ p.B L m)(pE:3*C.η ≤ 2) (uQ:(m:ℝ)*d+ C.γ*(1-degreePrice p.B C.γ C.η)⁻¹≤1)
    (hK:C.γ + Real.exp 1*(C.γ*(1-degreePrice p.B C.γ C.η)⁻¹ + m*d) ≤100*C.γ)
include v pD gA pE uQ hK
open Gas Ursell
lemma glowMoney (z:Key I)(v':z∈hill I):
    (∀ i, ForceB p i ((mkCup p F K u Fv z) i) h (rentH p (windF (paidLayers r a b u) (bagU (urnL (paidLayers r a b u)) (∑ i:I, μ i))) i)) ∧
    ∀ j:Seat Ω, (∑ i:Force _, giftK p (p.supportExponent+C.η) i j* rentH p (windF (paidLayers r a b u) (bagU (urnL (paidLayers r a b u)) (∑ i:I,μ i))) i) ≤ yσF p C := by
  obtain ⟨pU,t'⟩:= prepares K C σ X Fv μ A S V pD v gA z v' -- X maybe implicit args preserved
  obtain ⟨c0,c1⟩:= rackMoney C F K (Cube.node∘σ) q M X u v
  obtain ⟨r₀,fκ⟩:= layerSuit C F K (Cube.node∘σ) q M X u v z v'
  have he(X:Aura Ω): Aμ X ≤ m*d:=by
    obtain ⟨i,h⟩:=X.property; let hv:=currency p.B (p.supportExponent+1+1) X.val
    apply (le_mul_of_one_le_right (pU.1 X) (Real.one_le_exp (mul_nonneg (show 0≤p.supportExponent+1+1 from by linarith [p.exponent_pos]) (by positivity :0 ≤ (coverNumber p.B X.val:ℝ))))).trans; exact (single_le_sum (f:=fun x=> Aμ x*currency p.B (p.supportExponent+1+1) (x:Aura Ω).val) (fun i _=> mul_nonneg (pU.1 _) (Real.exp_pos _).le) (Finset.mem_filter.mpr ⟨mem_univ _,h⟩)).trans (t' i) -- tune
  have hη:=C.hη; have hX:=p.exponent_pos; have hy:0 ≤ σℓ:=by linarith
  obtain ⟨Q',e'⟩:= Vow.rent_x fκ pU.2 pU.1 c0 hy r₀ C.hη v X.timer.slope (fun i=> by rw [pow_zero,mul_one]; exact (add_le_add_left (he i) _).trans uQ) (fun i=>(tall_m _ pU.1 (b:=o+1+1) (by linarith) _).trans (t' i)) c1 C.degree (show (1/2:ℝ)<1 by norm_num) (mul_pos (by norm_num) C.hγ) (by rw [pow_zero,mul_one,←mul_assoc,mul_inv_cancel₀ (by linarith [X.timer.slope]),one_mul]; exact hK)
  refine reserveF (P:=p) _ _ Q' (fun i=> ?_) (zero_le_one.trans v) C.hη
  apply le_inv_mul_iff₀ (zero_lt_one.trans_le X.timer.slope) |>.2; exact (e' i).trans_eq (by ring)
end YM.CF.Vow.TreasuryFog

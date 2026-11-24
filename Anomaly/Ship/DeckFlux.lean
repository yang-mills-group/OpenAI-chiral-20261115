import Anomaly.Ship.Amble
import YM.CF.Roots.Seat
import YM.CF.Roots.Stem
import YM.CF.Rive.Wally
import YM.CF.Roots.Cost
import YM.CF.Roots.Watt
import YM.CF.Mew.Char
import YM.CF.Mew.Firth
import YM.CF.Neon.LatticeFieldEstimates
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 16000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Roots
open Function Finset Filter Metric MeasureTheory Lattice Lattice.Corona Wilson Precision Pressure RG
open Jet Fock Cube Lat Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
variable {n:Side}{u t B:ℕ}{C ε η a d:ℝ}
variable {J:Type}[LinearOrder J][Fintype J]{P:BudgetPoint}{h b v w:ℝ}
open Spire Tulip Mew
attribute [local instance] opCStarAlgebra
open scoped YM.CF.Mew
open Rive Neon Larch Vow Prism
local notation "κ"=>Force n
local notation "λQ"=> (P.supportExponent+1/2)
local notation "βo"=> P.supportExponent
local notation "λN"=> Finset J
variable (V:Finset (Finset J))(L: Finset J→ ForceBudget n) (σ:J→ Seat n)
variable (ht:0 < h) (C A:ℝ)(hpQ:∀ i∈ V,∀ x:Force n,L i x ≠0→ poke_F σ x.val.1.val.2 i)(E:∀ i∈ V,SanB (L i) (giftK P (P.supportExponent+(P.B:ℝ)⁻¹)) P h (fun _=>A))
private abbrev Φo(x:Force n):= x.val.1.val.2
local notation "ϕz"=> giftK P
include hpQ E ht
lemma forge_l_var : ∃ (f: Finset J→ Force n→ℝ), (∀ i∈V,∀ x, ForceB P x (L i x) h (f i x))∧(∀ i∈V,0≤f i)∧(∀ i∈V,∀ x:Force n,f i x ≠0→poke_F σ x.val.1.val.2 i)∧∀ i∈ V,∀ c: Seat n,(∑ x:Force n, giftK P (P.supportExponent+(P.B:ℝ)⁻¹) x c * f i x)≤ A:=by
 choose! f u k using fun i p=>(E i p).bit; let G(i x):ℝ:=if τ':L i x=0 then 0 else f i x; have h1(z h x):0 ≤ f z x:=gradeQ _ _ (u z h x) ht.le
 have he(i)(v:i∈V)(x:Force n):ForceB P x (L i x) h (G i x):=by
    unfold G; split
    next t=> rw [t]; exact Vale.rinsed ..
    next t=> exact u _ v _
 refine ⟨G,he,fun i p x=>gradeQ _ _ (he i p x) ht.le,fun i p x w=> hpQ _ p _ (fun v=>w (dif_pos v)),fun i p c=> (sum_le_sum fun j _=>?_).trans (k i p c)⟩
 unfold G; split; · refine mul_le_mul_of_nonneg_left (h1 _ p _) ?_; unfold giftK; split; exact (Real.exp_pos _).le; exact le_rfl
 exact le_rfl

variable (z:Finset J→ℂ)(hz:∀ i∈V,‖z i‖≤ C^i.card)(tC:1 ≤ C)(hk:8 ≤ P.B)(he:0 ≤A)(pc:Apex (cape_B P.B) P.B σ) (wt:lamp_B (cape_B P.B) P.B t σ)(uC: packF C P.B t)
include hz tC hk he pc wt uC
-- force funding issuance.
lemma sprint_K_var (ρ:∀ i∈V,Set.InjOn σ (i:Set J))(hi:∀ i∈V,1 < i.card): Dark (fun _=>False) (∑ i∈V,z i • (L i)) P h (chillCash P.B*A):=by
 obtain ⟨f,h,q,u,p⟩:=forge_l_var V L σ ht A hpQ E
 let C0(X):= ∑ i∈V,‖z i‖* f i X; refine ⟨⟨C0,fun Y=>?_ ,fun i=>?_⟩,fun _ p=>p.elim⟩
 · rw [Finset.sum_apply]; refine dom_K_fin Y V _ _ ?_; exact fun i p=> dúe _ _ (h i p _) _ -- dom_K index requires LinearOrder on Finset J (lattice partial not linear); need `Finset Lex` or adapt
 have hv:=α_argo (a:=P.supportExponent) σ i Φo (fun x=>i∈x.val.1.val.2) pc wt V f q (fun j p x s a=>⟨s,u j p x a⟩) A (fun j y=> p j y i) he z hz tC hk uC (fun i w=>⟨hi i w,ρ i w⟩) -- order.tactic
 apply le_trans ?_ hv; apply sum_le_sum; intro j p; unfold cocoa; split_ifs <;> first|exact le_rfl|simp

lemma tiny_GK (hi:∀ i∈V,i.card=1): Dark (fun _=>False) (∑ i∈V,z i • (L i)) P h (t*C*A+chillCash P.B*A):=by
 obtain ⟨f,h,q,u,p⟩:=forge_l_var V L σ ht A hpQ E
 let C0(X):= ∑ i∈V,‖z i‖* f i X; refine ⟨⟨C0,fun Y=>?_ ,fun i=>?_⟩,fun _ p=>p.elim⟩
 · rw [Finset.sum_apply]; refine dom_K_fin Y V _ _ ?_; exact fun i p=> dúe _ _ (h i p _) _
 have hv:=γ_argo (a:=P.supportExponent) σ i Φo (fun x=>i∈x.val.1.val.2) pc wt V f q (fun j p x s a=>⟨s,u j p x a⟩) A (fun j y=> p j y i) he z hz tC hk uC hi
 apply le_trans ?_ hv; apply sum_le_sum; intro j p; unfold cocoa; split_ifs <;> first|exact le_rfl|simp
end YM.CF.Roots

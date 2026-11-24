import YM.CF.Milo.Cent
import YM.CF.Sour.Cluck
import YM.CF.Fief.Lucid
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Inherited
import YM.CF.Sour.Lead
import YM.CF.Sour.Park
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Push.AbsoluteSums Nor Tenant
variable (P:BudgetPoint) (S:Support (More n))
variable {e a b:ℝ}
variable {F:Support (More n)→ Raw (Openc (More n) e) (Single n)}(M:Support (More n)→Toll (Single n))(Q:∀ S, Ticket (bail n e) (bail n e) S (M S) (F S))(w:Ledger a M b)(p:0<a)(v:a ≤1)(t: 2*P.supportExponent*Fief.tileN 1≤ a/2*P.B)
abbrev numV(P:BudgetPoint):=4+coinK P.order P.power
def growL (n i:ℕ)(x:ℝ):= x*n*i -- drop
abbrev oom(n:ℕ)(C:ℝ):= (C⁻¹)^n
abbrev tollL0 (o k:ℕ)(η:ℝ):=Real.exp (η*Fief.tileN 1)*gown o k
local notation "tL"=> tollL0 P.order P.power P.supportExponent
abbrev wingY(P:BudgetPoint)(x:ℕ):=tollL0 P.order P.power P.supportExponent*x -- drop
abbrev κY (P:BudgetPoint):=tollL0 P.order P.power P.supportExponent * Tenant.quota
local notation "uL"=> κY P
abbrev worth (S: SO):= Trees.currency P.B P.supportExponent (halo P.B S)*fareX 1 P S * ledgerV (M S)
variable (x:Seat n)
include Q
lemma shelf_s(S:SO):0 ≤ @worth _ P M S:=by unfold worth; exact mul_nonneg (mul_nonneg (Real.exp_pos ..|>.le) (health_f ..)) (sum_nonneg fun i _=> sum_nonneg fun j _=> (Q S).nonn i j)
include t p w
lemma rFee (j:ℕ) : (∑ S∈(hit0 x).filter (fun i=>i.card=j),worth P M S) ≤ κY P * b * (Real.exp (-a/2*j)*(j+1:ℝ)^numV P):=by
 let c:= coinK P.order P.power; let V:=(j+1:ℝ); let A:= tL; let R(U:SO):= Branch.rent (a/2) U*ledgerV (M U)
 have hA:0 ≤ tL:=by unfold tollL0 gown; positivity
 have he(S:SO)(k:S.card=j): worth P M S ≤ A*V^c*R S:=by
    unfold worth; let B:= ledgerV (M S); change _ * _*B ≤ _; by_cases hx:B=0; · rw [hx,mul_zero]; unfold R; unfold B at hx; rw [hx,mul_zero,mul_zero]
    have hs:0≤B:=sum_nonneg fun i _=> sum_nonneg fun j _=> (Q S).nonn i j
    obtain ⟨i,g,w'⟩:=exists_ne_zero_of_sum_ne_zero hx; obtain ⟨j',l,p'⟩:=exists_ne_zero_of_sum_ne_zero w'; have ht: Grove (terr _) S:= ((Q S).expo i j' |>.triggered p').1
    let T₀:= ConnectedActivityE6.Raw.atOne (More n); let k':=P.B; let A':=P.supportExponent; have h₀:A'≥0:=P.exponent_pos.le; have hK:=P.B_pos
    have hk:= Fief.fen T₀ S k' 1 hK a A' p h₀ (by rw [show T₀.count.val=1 from rfl]; simpa using t) ht; rw [one_mul, show S.image T₀.parent=S from (by rw [show T₀.parent=id from funext fun i=>ConnectedActivityE6.Raw.parent_one i,image_id])] at hk
    calc
      _ ≤ (Real.exp (A'*Fief.tileN 1)*Branch.rent (a/2) S)*(gown P.order P.power*(S.card+1:ℝ)^c)*B :=mul_le_mul_of_nonneg_right (mul_le_mul hk (moneyP P S ht) (health_f ..) ((Real.exp_pos ..).le.trans hk)) hs
      _ = A*V^c*R S:=by rw [k]; unfold A B V R tollL0 A'; ring -- tune notation.
 have hg:= covered_hit Q w p (meterQ n e) (le_trans (by norm_num :(0:ℝ)≤16) quota_bound) x j
 apply (sum_le_sum fun i v=> he i ((mem_filter.mp v).2)).trans; rw [←mul_sum]; refine (mul_le_mul_of_nonneg_left hg ?_).trans_eq ?_ ; unfold A; apply mul_nonneg hA; positivity
 unfold κY V A numV c; ring
include v
lemma rood_r : (∑ S∈hit0 x, worth P M S) ≤ κY P * b * (16 * fernL (numV P) * oom (numV P+1) a) :=by
 let V:=Fintype.card SA; let Y:= range (V+1)
 rw [←Finset.sum_fiberwise_of_maps_to (g:= Finset.card) (t:=Y) (fun _ _=>mem_range.mpr ((card_le_univ ..).trans_lt (by simp [V])))]; refine (sum_le_sum (fun j _=>rFee P M Q w p t x j)).trans ?_; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (pea a p v _ _) (mul_nonneg (mul_nonneg (by unfold tollL0 gown; positivity) (le_trans (by norm_num :(0:ℝ)≤16) quota_bound)) w.posP)
omit v
lemma stint (h:∀ S: Support (More n),S.card≠1→M S=0): (∑ S∈hit0 x,worth P M S) ≤ κY P *b*(2:ℝ)^numV P:=by
 let Y:=hit0 x; let U:=Y.filter fun i=>i.card=1; rw [← sum_subset (show U⊆ _ from filter_subset ..)]; swap; · intro i p k; unfold worth; rw [h i (fun v=>k (mem_filter.mpr ⟨p,v⟩))]; simp [ledgerV]
 apply (rFee P M Q w p t x 1).trans; refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (mul_nonneg (by unfold tollL0 gown; positivity) (le_trans (by norm_num :(0:ℝ)≤16) quota_bound)) w.posP)
 norm_num; linarith
end YM.CF.Sour

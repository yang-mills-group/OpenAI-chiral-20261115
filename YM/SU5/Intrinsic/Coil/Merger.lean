import YM.SU5.Intrinsic.Coil.Bedeck

/-! Compute finite density with all ticket powers. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Coil
open Function Lattice Finset Filter Stilo Palot RG Scree Skye
open Fock Tulip
open scoped BigOperators Classical YM.CF.Mew

namespace Chart
open Vow Rue
variable {I : Type}[Fintype I][DecidableEq I]{n:Side} (B:Chart I (Seat n))
variable (p:BudgetPoint) (U:I→ Cipher n →ₗ[ℂ] Cipher n) (P:ForceBudget n)
local notation "L"=> B.ledger
variable (Tape':List I)(Deck:List (Force n))
def reading (B:Chart I (Seat n))(U:I→ Cipher n →ₗ[ℂ] Cipher n)(Tape':List I): Cipher n →ₗ[ℂ] Cipher n:= ∑ S:Finset I with B.offices S, sail U S Tape'
lemma arrange (G:Finset (I⊕ Force n)→ Cipher n):
    ∑ S:Finset (I⊕ Force n),G S=∑ i:Finset I,∑ j:Finset (Force n), G (i.disjSum j):=by
 rw [←Fintype.sum_prod_type' (fun (i:Finset I) (j:Finset (Force n))=> G (i.disjSum j))]; apply Eq.symm
 apply Finset.sum_nbij' (fun v=> v.1.disjSum v.2) (fun v=>(v.toLeft,v.toRight)); exact fun _ _=> mem_univ _; exact fun _ _=> mem_univ _; simp; intro i _; ext x; cases x <;> simp
 intros; rfl -- parse semicolon scope tune

private lemma ahead(B:Chart I (Seat n)){S:Finset (Force n)}(x:Orbit n)(h:FleetS p.threshold x.1)(i:Force n)(q:i∈S)(v:coverF p S x.1)(u:procession S):
    clamp p i (P i) x=P i x:=by
 let A:= (∅:Finset I); have hx:B.offices A:=by change Set.InjOn _ (↑(∅:Finset I): Set I); rw [Finset.coe_empty]; exact Set.injOn_empty _
 let t:= ((B.fuel_iff A S x.1 p).2 ⟨hx,v,u⟩).2
 have hm:= B.sure_Flag t i (inr_mem_disjSum.mpr q)
 refine if_pos ((shoreK _ _ h _).mp (Finset.disjoint_left.mpr (fun j hb r=> ?_))) -- includes implicit j?
 exact (mem_sdiff.mp hb).2 (hm ▸ mem_inter.mpr ⟨(mem_sdiff.mp hb).1,r⟩)

lemma settles (d:Deck.Nodup)(z:Deck.toFinset=univ) (h:B.Mild U)(x:Orbit n)(q:FleetS p.threshold x.1)(F:∀ i,Pastry.Flour (camp (lordD i).val) (P i x).val):
    B.reading U Tape' (fueled p P x)=hGas (flags p.threshold x.1) (fun i=> B.script Tape' Deck (flags p.threshold x.1) U (fun i=>P i x) i.val):=by
 let T:= together Tape' Deck; let Ω:= flags p.threshold x.1
 let Z(f:Finset (I⊕ Force n)):= Album.traverse (readAt U (fun i=>P i x)) f T
 have he:B.ledger.Mounted Z (Ω:=Ω):= (B.moving_germ U (fun i=>P i x) h F).tour Ω T
 change B.reading U Tape' _ = hGas Ω (fun i=> (L).compact Z Ω i.val)
 rw [← B.ledger.gas_identity Z he, Finset.sum_filter,arrange, reading,LinearMap.sum_apply,Finset.sum_filter]; apply sum_congr rfl; intro s _
 by_cases y:B.offices s; swap
 · rw [if_neg y]; symm; apply sum_eq_zero; intro i _; exact (if_neg fun t=>y ((B.fuel_iff s i x.1 p).mp t).1)
 rw [if_pos y,fueled,map_sum]; apply sum_congr rfl; intro i _
 by_cases g:coverF p i x.1∧ procession i
 · rw [if_pos g,if_pos ((B.fuel_iff _ _ _ p).2 ⟨y,g⟩), prod_congr rfl (fun i hi=> ahead p P B x q i hi g.1 g.2)] -- unfold Z?
   exact (execute s i U (fun i=>P i x) Tape' Deck d z).symm
 rw [if_neg g,map_zero,if_neg (fun u=> g ((B.fuel_iff s i x.1 p).1 u).2)]

end Chart
end YM.CF.Coil
open YM.CF.Coil
#print axioms Chart.settles

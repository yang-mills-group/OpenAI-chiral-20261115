import YM.CF.BProof.Moment.Book

/-! Sums of a finite family of pricers. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Moment.Bill
open Filter Set RG Wilson Lattice Finset Function Push.AbsoluteSums MeasureTheory Micro
open scoped Topology BigOperators Classical
variable {s:Side}{G:Gauge}{I:Type*}

def kit (B:Finset I)(F:I→Bill s G): Bill s G where
 amount T:=∑ i∈ B,(F i).amount T
 tax T U:=∑ i∈ B,(F i).tax T U
 meas T:= (Envelope.sum _ _ (fun i=> (F i).tax_ep _)).meas
 stops T U V h:= sum_congr rfl fun i _=>(F i).stops T U V h
 owned T t U:= sum_congr rfl fun i _=> (F i).owned T t U
 enough T U:= (norm_sum_le _ _).trans (sum_le_sum fun i _=> (F i).enough T U)
 roots T h:=by
   by_contra u; apply h; apply sum_eq_zero; intro i _; exact not_not.mp (fun h=>u ((F i).roots T h))
lemma kit_price (B:Finset I)(F:I→Bill s G)(U:Config G s): (kit B F).price U=∑ i∈ B,(F i).price U:=sum_comm
lemma kit_fine (B:Finset I)(F:I→Bill s G){r:ℝ}{C:I→ℝ}(h:∀ i∈ B,(F i).fine r (C i)): (kit B F).fine r (∑ i∈B,C i) := by
 refine ⟨(kit B F).amount_p,fun o=>?_⟩; convert budget_over B (fun i x=> hit id (F i).amount r o x) C (fun i l=>(h i l).pays o) using 1; ext x; unfold hit; split_ifs <;>simp [kit,Finset.mul_sum]
end YM.CF.BProof.Moment.Bill

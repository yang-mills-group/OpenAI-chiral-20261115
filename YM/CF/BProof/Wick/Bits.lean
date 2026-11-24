import YM.CF.BProof.Wick.Melt

/-! Mark-site occupation projection; even. Tensor convention implemented by using
these embedded operators directly on Single N. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Wick
open Function Filter NormedSpace Fock Thera Finset Branch Align
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][LinearOrder I]{p q S: Finset I}
lemma cabin_basis (p q s: Finset I): acts (cabin p q) (basisKet s)= if s∈permit p q then basisKet s else 0:= cut_basis ..
lemma cabin_proj (p q:Finset I): IsStarProjection (cabin p q):= cutM_idp _
lemma cabin_merge (p q r s:Finset I): cabin (p∪r) (q∪s)=cabin p q*cabin r s:=by
 apply op_columns; intro i; rw [act_mul, cabin_basis,cabin_basis]; have h : i∈permit (p∪r) (q∪s) ↔ i∈permit p q ∧ i∈permit r s:= by simp only [permit_rule,Finset.union_subset_iff, disjoint_union_left]; tauto
 by_cases g:i∈permit r s; by_cases e:i∈permit p q <;> simp only [h,e,g,↓reduceIte,and_true,cabin_basis]; rw [if_neg g,if_neg (fun j=>g (h.mp j).2),map_zero]
lemma cabin_nil : cabin (∅:Finset I) ∅=1:=by apply op_columns; intro i; rw [cabin_basis]; simp
lemma capOne(i:I): cabin {i} ∅= put i*takeF i:=by apply op_columns; intro j; rw [cabin_basis,occ_act]; simp
lemma capZero(i:I): cabin (∅:Finset I) {i}=takeF i*put i:=by apply op_columns; intro j; rw [cabin_basis,vacant_act]; simp -- maybe not
lemma tagged (h:p⊆S)(k:q⊆S): Fock.Sector S false (cabin p q):=by
 induction p using Finset.induction_on with
 | empty =>
   induction q using Finset.induction_on with
   | empty=> rw [cabin_nil]; exact Sector.one
   | insert i t g ih=>
     rw [←singleton_union,←empty_union (∅:Finset I),cabin_merge]; rw [capZero]
     exact ((Sector.down i (k (mem_insert_self ..))).mul (Sector.up i (k (mem_insert_self ..)))).mul (ih ((subset_insert ..).trans k))
 | insert i p g ih=> rw [← singleton_union, ← empty_union q, cabin_merge, capOne]; exact ((Sector.up i (h (mem_insert_self ..))).mul (Sector.down i (h (mem_insert_self ..)))).mul (ih ((subset_insert ..).trans h))
lemma stopCap (p q:Finset I)(i:I)(h:i∈p):put i*cabin p q=0:=by
 apply op_columns; intro x; rw [act_mul,act_zero,cabin_basis]; split; rw [put_act,if_pos (((permit_rule ..).1 ‹_›).1 h)]; exact map_zero _
lemma stopEmpty(p q:Finset I)(i:I)(h:i∈q): takeF i*cabin p q=0:=by
 apply op_columns; intro x; rw [act_mul,act_zero,cabin_basis]; split; rw [take_act,if_neg (disjoint_left.mp (((permit_rule ..).1 ‹_›).2) h)]; exact map_zero _
end YM.CF.BProof.Wick

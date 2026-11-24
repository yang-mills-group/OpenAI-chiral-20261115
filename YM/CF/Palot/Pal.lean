import YM.CF.Palot.Kali
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Palot
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo
open scoped Classical
variable {A I E:Type*}[Fintype A][DecidableEq A][Fintype I][DecidableEq I][CommSemiring E]
abbrev Crowd(A:Type*):= Harper A
local notation "bay"=> Stilo.bay
def fits(X:I→leaf A)(P:Finset I)(H:Crowd A):Prop:=∀ i∈P,beamH (X i).val ≤ H
structure Org (X:I→leaf A)(F:Finset I→ Track (Crowd A) E):Prop where
 loft i h:F i h≠0→fits X i h
 loaf:F ∅ ⊥ =1
 stitch(S T: Crowd A)(i j: Finset I): Disjoint (bay S) (bay T)→fits X i S→ fits X j T→ F (i∪j) (S⊔T)= F i S* F j T
variable {X:I→leaf A}{F:Finset I→Track (Crowd A) E}{i j:Finset I}{H R:Crowd A}
def cutH (X:I→leaf A)(H:Crowd A)(P: Finset I):Finset I:= P.filter fun i=> beamH (X i).val ≤ H
lemma atop (h: Org X F)(S:Crowd A):∑ i:Finset I,F i S=∑ i:Finset I with fits X i S,F i S:= (sum_filter_of_ne fun i _ p=> h.loft i S p).symm
lemma fits_i{a:I} (p:beamH (X a).val ≤ H)(h:beamH (X a).val ≤ R): ¬ Disjoint (bay H) (bay R):=by
 obtain ⟨i,g⟩:=(X a).property; have hx : i∈ bay (beamH (X a).val):=(bay_beam (X a).val).symm ▸ g; exact fun u=> Finset.disjoint_left.mp u (bay_m p hx) (bay_m h hx)
lemma ads(p:Disjoint (bay H) (bay R))(h: fits X i H)(q:fits X j R): cutH X H (i∪j)=i:=Finset.ext fun a=>by
 rw [cutH,mem_filter]; constructor
 · rintro ⟨t,l⟩; exact (mem_union.mp t).resolve_right fun g=> fits_i l (q _ g) p
 intro u; exact ⟨mem_union_left _ u,h _ u⟩
def mintF(F:Finset I→ Track (Crowd A) E)(H:Crowd A):E:= ∑ i:Finset I,F i H
lemma adC (h: Org X F)(p:Disjoint (bay H) (bay R)) : mintF F (H⊔R)=mintF F H *mintF F R:=by
 unfold mintF; rw [atop h, atop h, atop h,sum_mul_sum,← sum_product']; symm
 refine sum_nbij' (fun a=>a.1∪a.2) (fun i=>(cutH X H i,cutH X R i)) ?_ ?_ ?_ ?_ ?_
 · rintro ⟨i,j⟩ g; obtain ⟨l,r⟩:=mem_product.mp g; refine mem_filter.mpr ⟨mem_univ _,?_ ⟩; intro k ht; exact (mem_union.mp ht).elim (fun t=>((mem_filter.mp l).2 k t).trans le_sup_left) (fun t=> ((mem_filter.mp r).2 k t).trans le_sup_right)
 · intro i g; exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,fun _ p=>(mem_filter.mp p).2⟩,mem_filter.mpr ⟨mem_univ _,fun _ p=> (mem_filter.mp p).2⟩⟩
 · rintro ⟨i,j⟩ g; obtain ⟨l,t⟩:= mem_product.mp g; let H':=(mem_filter.mp l).2; let T':= (mem_filter.mp t).2; exact Prod.ext (ads p H' T') (by dsimp only; rw [union_comm,ads p.symm T' H']) -- tune
 · intro a g; refine Finset.Subset.antisymm (union_subset (filter_subset ..) (filter_subset ..)) ?_; intro i t
   exact (beam_choice p _ ((mem_filter.mp g).2 i t)).elim (fun l=>mem_union_left _ (show i∈ cutH X H a from mem_filter.mpr ⟨t,l⟩)) (fun l=> mem_union_right _ (show i∈ cutH X R a from mem_filter.mpr ⟨t,l⟩))
 rintro ⟨i,j⟩ g; obtain ⟨l,u⟩:= mem_product.mp g; exact (h.stitch H R i j p (mem_filter.mp l).2 (mem_filter.mp u).2).symm
lemma nilP(h:Org X F):mintF F ⊥=1:=by
 rw [mintF,sum_eq_single ∅,h.loaf]; intro b _ l; obtain ⟨y,v⟩:=nonempty_iff_ne_empty.mpr l; by_contra p; exact fits_i (h.loft b ⊥ p y v) (h.loft b ⊥ p y v) (by simp [bayB]); simp -- tune
lemma flyP(h:Org X F)(i:Finset (leaf A))(p:flow A i): mintF F (weighH i)= ∏ j∈ i,mintF F (beamH j.val):=by
 induction i using Finset.induction_on with
 | empty=> rw [weighH,Finset.sup_empty, nilP h,prod_empty]
 | @insert i s k ih=>
    have hp:= flow_m p (subset_insert i s); have hx: Disjoint (bay (beamH i.val)) (bay (weighH s)):=by rw [bay_beam,(weigh_i hp).1]; exact flow_d p k
    rw [prod_insert k,show weighH (insert i s)=beamH i.val⊔weighH s from (by simp [weighH]), adC h hx, ih hp]
-- canonical gas, includes exact external flags E touched; use disjoint selection with healthy complements externally later
abbrev hook(A:Type*):= Finset (leaf A)
def hGas(O:Finset A)(U:leaf A→ E):E:=∑ i:hook A with flow A i ∧ O⊆robe i, ∏ j∈i,U j
lemma chimeU (O:Finset A)(h: Org X F):∑ i: Finset I,∑ H:Crowd A with O⊆bay H,F i H=hGas O (fun i:leaf A=>mintF F (beamH i.val)):=by
 rw [hGas,sum_comm]; change ∑ H:_ with _,mintF F H=_
 apply sum_nbij' tally weighH; intro i p; exact mem_filter.mpr ⟨mem_univ _,flagship i,(mem_filter.mp p).2.trans_eq (bay_t i)⟩ -- tune .trans_eq not subset
 intro i p; obtain ⟨l,t⟩:= (mem_filter.mp p).2; exact mem_filter.mpr ⟨mem_univ _,t.trans_eq (weigh_i l).1.symm⟩
 exact fun i _=> tale_H i
 exact fun i p=> emblem (mem_filter.mp p).2.1
 exact fun i _=> (congrArg _ (tale_H i).symm).trans (flyP h _ (flagship i)) -- _
end YM.CF.Palot

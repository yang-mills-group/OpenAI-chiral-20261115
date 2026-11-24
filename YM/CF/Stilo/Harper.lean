import YM.CF.Proa.Wings
import YM.CF.Scree.Locus
set_option autoImplicit false
noncomputable section
/-! Parent-incidence book for CAR/Wick. Each hyperlocation registers a full clique,
not assuming geometric connectedness inside that set. -/
namespace YM.CF.Stilo
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {X:Type*}[Fintype X][DecidableEq X]{x y:X}
structure Harper (X:Type*) where -- fix
 pair:Finset (X×X)
 flip {i j}: (i,j) ∈ pair → (j,i) ∈ pair
 tran {i j k}: (i,j)∈ pair → (j,k)∈ pair → (i,k)∈ pair
@[ext] lemma harp_ext {i j: Harper X}(h:i.pair=j.pair):i=j:=by cases i; cases j; congr
instance: Fintype (Harper X):=let _ : Finite (Harper X):=Finite.of_injective Harper.pair (fun _ _ h=> harp_ext h); Fintype.ofFinite _
abbrev rail (H : Harper X)(p q:X):Prop:= (p,q) ∈ H.pair
def subA (A B: Harper X) := A.pair ⊆ B.pair
instance pHa : PartialOrder (Harper X) := PartialOrder.lift Harper.pair (fun _ _ h=>harp_ext h)
def joinH(A B:Harper X):Harper X:= {
 pair:= univ.filter fun i=>TransGen (fun a b=> rail A a b ∨ rail B a b) i.1 i.2
 flip:=fun {i j} h=> by
    let p:=fun a b=> rail A a b ∨ rail B a b; have hp : TransGen p i j := (mem_filter.mp h).2
    refine mem_filter.mpr ⟨mem_univ _,?_⟩; dsimp only; change TransGen p _ _
    clear h; induction hp with
    | single h=> exact TransGen.single (h.elim (fun x=>Or.inl (A.flip x)) fun x=>Or.inr (B.flip x))
    | tail h v ih=> exact ih.head (v.elim (fun x=>Or.inl (A.flip x)) fun x=>Or.inr (B.flip x))
 tran:=fun {i j k} p q=> by
    let P:=fun a b=> rail A a b ∨ rail B a b; exact mem_filter.mpr ⟨mem_univ _,(show TransGen P i j from (mem_filter.mp p).2).trans (show TransGen P j k from (mem_filter.mp q).2)⟩ }
instance supH: SemilatticeSup (Harper X) where
 sup:=joinH
 le_sup_left i j:=fun k h=>mem_filter.mpr ⟨mem_univ _,TransGen.single (Or.inl (by exact h))⟩
 le_sup_right i j:=fun k h=>mem_filter.mpr ⟨mem_univ _,TransGen.single (Or.inr h)⟩
 sup_le A B C t u:=fun ⟨i,j⟩ h=>by
    let P:=fun a b=> rail A a b ∨ rail B a b; change rail C i j; have hh:TransGen P i j:=(mem_filter.mp h).2; clear h; induction hh with
    | single h=> exact h.elim (@t _) (@u _)
    | tail _ v ih => exact C.tran ih (v.elim (@t _) (@u _))
instance botH:OrderBot (Harper X):={ bot:=⟨∅, fun e=>False.elim (notMem_empty _ e), fun g _=> False.elim (notMem_empty _ g)⟩, bot_le:=fun _=>Finset.empty_subset _ }
def beamH (S:Finset X): Harper X:={ pair:= S ×ˢ S, flip:= fun h=>mem_product.mpr ⟨(mem_product.mp h).2,(mem_product.mp h).1⟩, tran:=fun a b=>mem_product.mpr ⟨(mem_product.mp a).1,(mem_product.mp b).2⟩ }
lemma beam_b:beamH (∅ : Finset X)=⊥:= harp_ext (by change ∅ ×ˢ ∅=∅; simp)
def bay(H:Harper X):Finset X:= univ.filter fun i=> rail H i i
lemma bayH {A:Harper X} {x:X}:x∈bay A ↔ rail A x x:=mem_filter.trans (and_iff_right (mem_univ _))
lemma beam_l(A B:Finset X):beamH A≤beamH B ↔ A⊆B:=⟨fun h x p=> (mem_product.mp (@h (x,x) (show rail (beamH A) x x from mem_product.mpr ⟨p,p⟩))).1,fun p i h=> mem_product.mpr ⟨p (mem_product.mp h).1,p (mem_product.mp h).2⟩⟩
lemma bayM (A : Harper X):A ≤ beamH (bay A):=fun ⟨i,j⟩ p=>mem_product.mpr ⟨bayH.mpr (A.tran p (A.flip p)),bayH.mpr (A.tran (A.flip p) p)⟩
lemma boundH (A B:Finset X) (p:¬Disjoint A B) : beamH A⊔beamH B=beamH (A∪B):=by
 obtain ⟨x,l,r⟩:= Finset.not_disjoint_iff.mp p; apply le_antisymm (sup_le ((beam_l ..).mpr Finset.subset_union_left) ((beam_l ..).mpr Finset.subset_union_right)); let S:=beamH A⊔beamH B
 have he :beamH A ≤ S:=le_sup_left; have hj:beamH B ≤ S:=le_sup_right
 have ht(i:X)(h:i∈A∪B):rail S i x:= (mem_union.mp h).elim (fun k=>@he _ (show rail (beamH A) _ _ from mem_product.mpr ⟨k,l⟩)) (fun k=>@hj _ (show rail (beamH B) _ _ from mem_product.mpr ⟨k,r⟩))
 intro ⟨i,j⟩ p; have hx := mem_product.mp (show (i,j) ∈ (A∪ B) ×ˢ (A∪ B) from p); exact S.tran (ht i hx.1) (S.flip (ht j hx.2))
end YM.CF.Stilo

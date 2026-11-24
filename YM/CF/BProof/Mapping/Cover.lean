import YM.CF.BProof.Mapping.Grid

/- connected components, ledger projections. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Grid
open Lattice Finset Filter Function Relation
open scoped Topology BigOperators Classical
variable {n:ℕ}{s: Fin n→ Side}(k:ℕ)
namespace Part
variable (S T: Sites s)(x y:Vertex s)
def range := S.filter (fun y=> PathIn S k x y)
def parts := S.image (range k S)
variable {S T k x y}
@[simp] lemma out : y∈ Part.range k S x↔ y∈ S ∧ PathIn S k x y:=Finset.mem_filter
lemma base (h:x∈S):x∈Part.range k S x:=out.mpr ⟨h,.refl⟩
lemma cap {V} : Part.range k S x⊆ V ↔ ∀ y∈S, PathIn S k x y → y∈V:=by simp [Finset.subset_iff]
lemma subset (x:Vertex s): Part.range k S x⊆S:=filter_subset ..
lemma part_of (h:x∈ S)(k:ℕ): Part.range k S x ∈ parts k S:= mem_image_of_mem _ h
lemma congr' (h:PathIn S k x y): Part.range k S x=Part.range k S y:=by
 ext u; simp only [out]; exact and_congr_right (fun hu=> ⟨fun v=> (sym h).trans v, fun v=> h.trans v⟩)
lemma own (h:T∈ parts k S)(p:x∈T): x∈ S ∧ Part.range k S x = T:=by
 obtain ⟨a,ha,rfl⟩:=mem_image.mp h; exact ⟨(out.mp p).1,(congr' (out.mp p).2).symm⟩
lemma stays (h:x∈ S)(p:PathIn S k x y): PathIn (Part.range k S x) k x y:=by
 induction p with
 | refl=>exact .refl
 | @tail y z m u ih=> exact ih.tail ⟨out.mpr ⟨u.1,m⟩,out.mpr ⟨u.2.1,m.tail u⟩,u.2.2⟩
lemma geo (h:T∈parts k S): Conn T k∧ T⊆S∧ T.Nonempty:=by
 obtain ⟨a,p,rfl⟩:=mem_image.mp h; exact ⟨fun i hi j hj=> (sym (stays p (out.mp hi).2)).trans (stays p (out.mp hj).2),subset _,a,base p⟩
lemma pair (S:Sites s) (k:ℕ): ((parts k S):Set (Sites s)).PairwiseDisjoint id:= fun U u V v p=> disjoint_left.mpr (fun x h k=> p ((own (mem_coe.mp u) (x:=x) h).2.symm.trans (own (mem_coe.mp v) k).2))
lemma union (S:Sites s)(k:ℕ): (parts k S).biUnion id=S:=by
 ext x; rw [mem_biUnion]; exact ⟨fun ⟨I,p,v⟩=> (geo p).2.1 v, fun p=>⟨Part.range k S x,part_of p k,base p⟩⟩
lemma cost (S:Sites s)(k:ℕ): ∑ T∈ parts k S, T.card=S.card:= (card_biUnion (pair S k)).symm.trans (congrArg Finset.card (Part.union S k))
-- On a connected T, selected by predicate Z, each component touches internal boundary unless T⊆ Z.
lemma boundary {S T U:Sites s}(h:T∈ parts k (S∩U)) (p:Conn S k)(v:¬ S⊆ U): ∃ x∈T,∃ y∈ S, y∉U ∧ Grid.dist x y ≤ k:=by
 obtain ⟨x,hx⟩:= (geo h).2.2; have hV:= (geo h).2.1; have hp:T⊆ S:=hV.trans inter_subset_left; by_contra! q; apply v; intro y hy
 apply (hV.trans inter_subset_right : T⊆U) (x:=y); induction p x (hp hx) y hy with
 | refl=> exact hx
 | @tail i j a u ih=>
   have hi:= ih u.1; have hv:j∈U:= Classical.byContradiction (fun e=> (q i hi j u.2.1 e).not_ge u.2.2); rw [← (Part.own h hi).2]; exact out.mpr ⟨mem_inter.mpr ⟨u.2.1,hv⟩,.single ⟨hV hi,mem_inter.mpr ⟨u.2.1,hv⟩,u.2.2⟩⟩
end Part
lemma collar_conn (S:Sites s)(r:ℕ)(h:Conn S 1): Conn (collar S r) 1 := by
 let X(i:Vertex s):= collar ({i}:Sites s) r
 have hv:(Grid.collar S r)=S ∪ S.biUnion X:= by
   ext j; have ha: j∈Grid.collar S r ↔ j∈ S.biUnion X:=by simp [X]
   rw [ha,mem_union]; apply Iff.symm; exact or_iff_right_of_imp (fun e=>ha.1 (to_collar S r e)) -- tune
 rw [hv]; exact pile S h X (fun i _=> Prox.collar_solid r i) (fun i hi=> ⟨i,hi,to_collar _ _ (mem_singleton_self _)⟩)
end YM.CF.BProof.Grid

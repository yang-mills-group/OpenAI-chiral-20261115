import YM.CF.Stilo.Bubble
set_option autoImplicit false
noncomputable section
namespace YM.CF.Stilo
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {B:Type*}[Ring B]{A:Type*}[Fintype A][DecidableEq A]{H R P: Harper A}
lemma bayB : bay (⊥:Harper A)=∅:=eq_empty_iff_forall_notMem.mpr fun i h=>notMem_empty _ (bayH.mp h)
lemma bay_m (h:H ≤ R): bay H ⊆ bay R :=fun _ p=> bayH.mpr (@h _ (bayH.mp p))
lemma tract(a b:A)(h:rail H a b): (a∈bay H ∧ b∈ bay H):=by have ht:=bayM H; exact mem_product.mp (@ht (a,b) h) -- syntax
private lemma hob(h:Disjoint (bay H) (bay R))(x y z: A)(u: rail H x y ∨ rail R x y)(p : rail H y z ∨ rail R y z): rail H x z∨rail R x z:=by
 rcases u with i|j<;> rcases p with k|l
 · exact Or.inl (H.tran i k)
 · exact False.elim (Finset.disjoint_left.mp h (tract _ _ i).2 (tract _ _ l).1)
 · exact False.elim (Finset.disjoint_left.mp h (tract _ _ k).1 (tract _ _ j).2)
 exact Or.inr (R.tran j l)
lemma hut (h: Disjoint (bay H) (bay R)) {x y:A}: rail (H⊔R) x y ↔ rail H x y ∨ rail R x y:=by
 constructor
 · intro g; have hv : TransGen (fun x y=> rail H x y∨rail R x y) x y:= (mem_filter.mp g).2
   clear g; induction hv with
   | single t=>exact t
   | tail _ v ih=> exact hob h _ _ _ ih v
 have hh: H≤ H⊔R:=le_sup_left; have ht:R ≤ H⊔R:=le_sup_right; intro v; exact v.elim (@hh _) (@ht _)
lemma splits_eq (h:Disjoint (bay H) (bay R)) {Q: Harper A}(p:P ≤ H)(q:Q ≤ R)(hv:P⊔Q=H⊔R): P=H∧Q=R:=by
 have h1 {L B C D:Harper A}(h: Disjoint (bay L) (bay B))(p:C ≤ L)(q:D ≤ B)(hv:C⊔D=L⊔B):C=L:=by
    apply p.antisymm; intro ⟨i,j⟩ t
    let he:= (hut h).mpr (Or.inl (show rail L i j from t)); rw [←hv] at he; refine ((hut (Disjoint.mono (bay_m p) (bay_m q) h)).mp he).elim (fun z=>z) (fun g=>?_)
    exact False.elim (Finset.disjoint_left.mp h (tract _ _ (show rail L i j from t)).1 (bay_m q (tract _ _ g).1))
 refine ⟨h1 h p q hv,h1 h.symm q p (by rw [sup_comm Q,sup_comm R,hv])⟩
abbrev shutS (S: Harper A) (W:Track (Harper A) B): Track (Harper A) B:= fun i=> if i ≤ S then W i else 0
lemma contained_mul (h: Disjoint (bay H) (bay R)) (W U:Track (Harper A) B): crank (shutS H W) (shutS R U) (H⊔R)= W H*U R:=by
 unfold crank coal; simp_rw [Finset.sum_apply]
 rw [sum_eq_single H, sum_eq_single R, shutS,shutS,if_pos le_rfl,if_pos le_rfl]; exact Pi.single_eq_same ..
 · intro b _ l; unfold shutS; by_cases v:b ≤ R; · rw [Pi.single_eq_of_ne (fun p=>l ((splits_eq h le_rfl v p.symm).2))]
   rw [if_neg v,mul_zero,Pi.single_zero]; rfl
 · simp
 · intro a _ p; apply sum_eq_zero; intro b hv; unfold shutS
   split_ifs with c v
   · rw [Pi.single_eq_of_ne (fun t=>p (splits_eq h c v t.symm).1)]
   all_goals simp
 simp
-- truncate view via meet at imposed H
instance sinf: Min (Harper A):= ⟨fun X Y=> ⟨X.pair∩Y.pair,fun p=>mem_inter.mpr ⟨X.flip (mem_inter.mp p).1,Y.flip (mem_inter.mp p).2⟩, fun p h=>mem_inter.mpr ⟨X.tran (mem_inter.mp p).1 (mem_inter.mp h).1,Y.tran (mem_inter.mp p).2 (mem_inter.mp h).2⟩⟩⟩
instance land:SemilatticeInf (Harper A) where
 inf:=min
 inf_le_left _ _ := inter_subset_left
 inf_le_right _ _ := inter_subset_right
 le_inf _ _ _ p q:= subset_inter p q
lemma shut_view(H: Harper A)(W:Track (Harper A) B)(R:Harper A): view R (shutS H W)=view (R⊓H) W:=by
 unfold view shutS; rw [←sum_filter,show (deckX R).filter _=deckX (R⊓H) from Finset.ext fun i=> by simp only [mem_filter, deckH, le_inf_iff]]
lemma localizes(h:Disjoint (bay H) (bay R))(X Y Z:Track (Harper A) B)(w:∀ i,i ≤ H⊔R→ view i X=view (i⊓ H) Y * view (i⊓R) Z): X (H⊔R)=Y H*Z R:=by
 rw [←contained_mul h]; exact proves fun i p=>by rw [view_crank, shut_view, shut_view,w _ p]
lemma beam_choice (h:Disjoint (bay H) (bay R))(X:Finset A)(p:beamH X≤H⊔R): beamH X ≤ H ∨ beamH X ≤ R:=by
 by_contra! k
 have he(A':Harper A)(h:¬beamH X≤ A'):∃ i∈X,∃ j∈X,¬rail A' i j:=by
    by_contra! g; exact h fun ⟨i,j⟩ l=>g _ (mem_product.mp l).1 _ (mem_product.mp l).2
 obtain ⟨i,a,j,b,c⟩:=he _ k.1; obtain ⟨i',x,j',y,z⟩:=he _ k.2
 have hv(w)(p':w∈X)(u)(q:u∈X):rail H w u ∨ rail R w u:= (hut h).mp (@p (w,u) (mem_product.mpr ⟨p',q⟩))
 have ha:i∈bay R:= (tract _ _ ((hv i a j b).resolve_left c)).1; have hh:i'∈bay H:= (tract _ _ ((hv i' x j' y).resolve_right z)).1
 exact (hv i a i' x).elim (fun t=> Finset.disjoint_left.mp h (tract _ _ t).1 ha) (fun t=> Finset.disjoint_left.mp h hh (tract _ _ t).2)
end YM.CF.Stilo

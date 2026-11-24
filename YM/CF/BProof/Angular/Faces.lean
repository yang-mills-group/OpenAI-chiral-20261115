import YM.CF.BProof.Angular.Vic
-- avoid heavy WilsonStartup

/-! Footprint and indexing of each type of face across gaps and bands. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Angular
open Function Lattice Mag RG MeasureTheory Wilson Finset Filter Cube Circle
open scoped Topology BigOperators Classical
variable {s:Side}(x:Per s)(p:Space s)(i:TAxis)
abbrev Cell (s:Side):= Face (Per s)
lemma four (p:Cell s) : touched p={p.1, p.1+step p.2.val.1, p.1+step p.2.val.1+step p.2.val.2, p.1+step p.2.val.2}:=by
 simp only [touched,visits,square,Step.vec_pos,Step.vec_neg,add_right_comm (b:=step p.2.val.1) (c:=step p.2.val.2), add_neg_cancel_right]; ext y; simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,mem_insert,mem_singleton]; tauto
lemma four_self (p:Cell s): p.1∈ touched p:=by rw [four]; exact mem_insert_self ..
lemma wet_t (a:Per s)(l:ℕ) (h:l+1<s.val): touched (nf x p i)⊆ strip a l ↔ along a x<l:=by
 rw [four]; simp only [insert_subset_iff,singleton_subset_iff,mem_strip]; unfold nf face; dsimp only; simp only [time_join,time_add,time_step,ite_true,Fin.succ_ne_zero,ite_false,add_zero]
 constructor; rintro ⟨v,g,_⟩; rw [along_succ (by omega)] at g; omega
 intro e; rw [along_succ (by omega)]; omega
lemma wet_p (a:Per s)(l:ℕ): touched (hf x p i)⊆ strip a l ↔ along a x≤l:=by
 rw [four]; simp only [insert_subset_iff,singleton_subset_iff,mem_strip]; unfold hf face; dsimp only; simp only [time_join,time_add,time_step,Fin.succ_ne_zero,ite_false,add_zero,and_self]

namespace Yard
variable (Y:Yard s)
abbrev Marked (c:Cell s) := ∃ a:Y.Index,touched c⊆ Y.band a
lemma marked_n : Y.Marked (nf x p i) ↔ ¬ ∃ a:Y.Index, along (Y.v a) x<Y.short := by
 constructor; rintro ⟨a,h⟩ ⟨b,e⟩; exact Y.edge_disjoint ((wet_t x p i (Y.u a) _ Y.lL).1 h) e
 intro e; rcases Y.edge_from x with h|h; exact ⟨_,(wet_t _ _ _ (Y.u _) Y.long Y.lL).2 h⟩; exact absurd ⟨_,h⟩ e
lemma marked_h : Y.Marked (hf x p i) ↔ ∀ a:Y.Index,0<along (Y.v a) x→ ¬along (Y.v a) x <Y.short :=by
 constructor
 · rintro ⟨a,h⟩ j u v; rcases Y.common a x ((wet_p _ _ _ _ _).1 h) v.le with ⟨hh,rfl⟩|⟨hh,rfl⟩; rw [hh,Y.v_in j] at v; omega; rw [hh,along_self] at u; omega
 intro h; rcases Y.edge_from x with u|u; exact ⟨_,(wet_p ..).2 u.le⟩; generalize he:Y.twinsBand x=a at *; have hx:0=along (Y.v a) x:= by by_contra ht; exact h a (Nat.pos_of_ne_zero (fun e=>ht e.symm)) u
 rw [← along_zero.mp hx.symm]; exact ⟨_,(wet_p ..).2 (Y.u_in a).le⟩
lemma unmark_center (c:Cell s)(h:¬Y.Marked c): ∃ a:Y.Index,Y.Gap a (time c.1):=by
 rcases whichFace c with ⟨x,p,i,rfl⟩|⟨x,p,i,rfl⟩
 · rw [marked_n] at h; obtain ⟨a,e⟩:= not_not.mp h; exact ⟨a,e.le⟩
 rw [marked_h] at h; push_neg at h; obtain ⟨a,e,hv⟩:=h; exact ⟨a,hv.le⟩
end Yard

lemma hf_ne_nf {x x':Per s}{p p':Space s}{i j:TAxis} : hf x p i≠ nf x' p' j:=fun h=> Fin.succ_ne_zero (f₁ i) (congrArg (fun p:Cell s=>p.2.val.1) h)
def plEquiv : ((Per s × Space s × TAxis) ⊕ (Per s × Space s × TAxis)) ≃ Cell s:=
 let f(p:Per s×Space s×TAxis):= nf p.1 p.2.1 p.2.2; let g(p:Per s×Space s×TAxis):= hf p.1 p.2.1 p.2.2
 Equiv.ofBijective (Sum.elim f g) (by
   have h {x y:Per s}{p q:Space s}{i j:TAxis} : f (x,p,i)=f (y,q,j)→ x=y∧ p=q∧ i=j:=by
      intro e; exact ⟨congrArg (fun p:Cell s=>time p.1) e, (space_join x p) ▸ (space_join y q) ▸ congrArg (fun i:Cell s=>space i.1) e, Fin.succ_inj.mp (congrArg (fun i:Cell s=> i.2.val.2) e)⟩ -- tune
   have v {x y:Per s}{p q:Space s}{i j:TAxis} : g (x,p,i)=g (y,q,j)→ x=y∧p=q∧i=j:=by
      intro e; refine ⟨congrArg (fun p:Cell s=>time p.1) e,(space_join x p) ▸ (space_join y q) ▸ congrArg (fun i:Cell s=>space i.1) e,?_⟩
      exact (show ∀ i j:Fin 3,(f₁ i).succ=(f₁ j).succ→(f₂ i).succ=(f₂ j).succ→i=j by decide) i j (congrArg (fun i:Cell s=> i.2.val.1) e) (congrArg (fun i:Cell s=> i.2.val.2) e)
   constructor
   · intro a b e; rcases a with ⟨a⟩|⟨a⟩ <;> rcases b with ⟨b⟩|⟨b⟩
     · obtain ⟨p,q,r⟩:= h (x:=a.1) (y:=b.1) e -- tune metas
       congr 1; exact Prod.ext p (Prod.ext q r)
     · exact False.elim (hf_ne_nf e.symm)
     · exact False.elim (hf_ne_nf e)
     obtain ⟨p,q,r⟩:= v (x:=a.1) (y:=b.1) e; congr 1; exact Prod.ext p (Prod.ext q r)
   intro i; rcases whichFace i with ⟨x,p,i,rfl⟩|⟨x,p,i,rfl⟩; exact ⟨.inl (x,p,i),rfl⟩; exact ⟨.inr (x,p,i),rfl⟩)
lemma nf_inj {x x':Per s}{p p':Space s}{i i':TAxis} (h: nf x p i=nf x' p' i'): (x,p,i)=(x',p',i'):= Sum.inl.inj ((plEquiv (s:=s)).injective (a₁:=.inl (x,p,i)) (a₂:=.inl (x',p',i')) h) -- tune
end YM.CF.BProof.Angular

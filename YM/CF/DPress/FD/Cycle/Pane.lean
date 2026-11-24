import YM.CF.DPress.FD.Cycle.Circuit
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD.Cycle
open List Filter Set
open scoped Topology BigOperators ENNReal Classical
open Function
variable {I:Type*}[Fintype I][DecidableEq I] (S:Equiv.Perm I)
abbrev Skin(I:Type*):=I→ C
variable (P:I→Finset C) {U V: Finset I} (x y:Skin I)
-- writes over U, preserving other data exactly.
def Fill (U:Finset I)(P:I→Finset C)(x:Skin I) :Finset (Skin I):= Finset.univ.filter fun F=> (∀ i∈U,F i∈ P i)∧ (∀ i∉ U,F i=x i)
lemma report(y:Skin I) : y ∈ Fill U P x ↔ (∀ i∈U, y i∈P i)∧∀ i∉U,y i=x i:=by simp [Fill]
variable {x y}{w:Skin I}
lemma answer (h:Disjoint U V)(p:x∈Fill U P w)(q:y∈Fill V P x): y∈Fill (U∪V) P w:=by
 obtain ⟨i,k⟩:= (report ..).1 p; obtain ⟨j,f⟩:= (report ..).1 q; refine (report ..).2 ⟨fun p v=>?_ ,fun p t=>?_ ⟩; · rcases Finset.mem_union.mp v with v|v; rw [f p (fun g=> Finset.disjoint_left.mp h v g)]; exact i p v; exact j p v
 exact (f p fun k=> t (Finset.mem_union_right _ k)).trans (k p fun k=> t (Finset.mem_union_left _ k))
lemma peel (h:Disjoint U V)(p:y∈Fill (U∪V) P x): ∃ w∈Fill U P x,y∈Fill V P w:=by
 let w(i):= if i∈U then y i else x i; obtain ⟨f,k⟩:= (report ..).1 p; refine ⟨w, (report ..).2 ⟨fun i v=>?_,fun i v=>if_neg v⟩,(report ..).2 ⟨fun i v=>f i (Finset.mem_union_right _ v),fun i t=>?_ ⟩⟩; · rw [show w i=y i from if_pos v]; exact f i (Finset.mem_union_left _ v)
 unfold w; split; rfl; next g=> exact k i fun l=> (Finset.mem_union.mp l).elim g t
lemma register {b y':Skin I}(h:Disjoint U V)(p:y∈Fill U P x)(q:y'∈Fill U P x)(v:b∈ Fill V P y)(w:b∈Fill V P y'): y=y':=by
 funext i; by_cases h':i∈U; swap; · exact (((report ..).1 p).2 i h').trans (((report ..).1 q).2 i h').symm
 have ht:i∉V:=Finset.disjoint_left.mp h h'; exact (((report ..).1 v).2 i ht).symm.trans (((report ..).1 w).2 i ht)
variable (x)
lemma block (h:Disjoint U V) (f:Skin I→ℝ) : ∑ i∈Fill (U∪V) P x,f i=∑ i∈Fill U P x,∑ j∈Fill V P i,f j:=by
 rw [← Finset.sum_biUnion (?_: _),show (Fill U P x).biUnion (Fill V P)=Fill (U∪V) P x from ?_]; swap
 · intro i t j v H; exact Finset.disjoint_left.mpr fun l p q=> H (register P h t v p q)
 ext i; rw [Finset.mem_biUnion]; exact ⟨fun ⟨j,p,q⟩=> answer P h p q,peel P h⟩
lemma one_step(i:I)(f:Skin I→ℝ): ∑ y∈ Fill {i} P x,f y=∑ j∈P i,f (update x i j):=by
 rw [← Finset.sum_image (f:=fun j=> f j) (s:=P i) (g:=fun j=> update x i j) (?_: _)]; congr 1; ext y; rw [Finset.mem_image,report]; constructor
 · rintro ⟨u,v⟩; refine ⟨y i,u i (Finset.mem_singleton_self _),?_⟩; funext j; by_cases h:j=i; subst j; simp; exact (update_of_ne h ..).trans (v _ (by simpa using h)).symm
 · rintro ⟨u,v,rfl⟩; simp [v]; exact fun j h => Function.update_of_ne h ..  -- update notation ambiguity
 intro j v k w h; simpa using congrFun h i -- order?
@[simp] lemma entry : Fill ∅ P x={x}:=by ext i; simp [report,funext_iff]
lemma stamp (y:List I)(v:y.Nodup)(f:Word→ℝ):evalP P y f=∑ z∈Fill y.toFinset P x,f (y.map z):=by
 induction y generalizing f x with
 |nil=> simp [evalP]
 |cons i y h=>
    obtain ⟨u,t⟩:= nodup_cons.mp v; rw [List.toFinset_cons,←Finset.singleton_union,block P x (show Disjoint {i} y.toFinset from by simpa using u),one_step,evalP]; refine Finset.sum_congr rfl ?_; intro j v; rw [h (Function.update x i j) t (fun k=>f (j::k))]; -- order inspect
    refine Finset.sum_congr rfl fun z σ=>?_ ; rw [List.map_cons,((report ..).1 σ).2 i (by simpa),update_self]
end YM.CF.DPress.FD.Cycle

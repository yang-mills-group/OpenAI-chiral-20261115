import YM.CF.BProof.Contour.Growth

/- finite disjoint-gas estimate used at last step of B-contour. root-site recursion
for the B-rootK absolute log-bound needed there (only lower bound on magnitude).
Not replacing gas sum by supremum/variation. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Contour
open Function Moment Finset Relation Push.AbsoluteSums
open scoped Topology BigOperators Classical
variable {B I: Type*}[Fintype B][DecidableEq B][Fintype I][DecidableEq I]
variable (S:I→Finset B)(f:I→ℂ)(u:I→ℝ)
def hull (p:Finset I):=p.biUnion S
def flock (p:Finset I):Prop:= (↑p:Set I).PairwiseDisjoint S
lemma flock_zero : flock S ∅:= by simp [flock]
lemma flock_down (p q:Finset I)(h:p⊆q)(g:flock S q): flock S p:= Set.PairwiseDisjoint.subset g h
lemma hull_down(p q:Finset I)(h:p⊆ q): hull S p⊆ hull S q:=fun i g=> by obtain ⟨i,v,k⟩:=mem_biUnion.mp g; exact mem_biUnion.mpr ⟨i,h v,k⟩ -- tune
lemma hull_sub (P:Finset I)(i:I)(g:i∈P): S i⊆ hull S P:= fun j h=> mem_biUnion.mpr ⟨_,g,h⟩
lemma shrinkF {P:Finset I}(i:I)(h:i∉ P): flock S (insert i P) ↔ Disjoint (S i) (hull S P)∧ flock S P:=by
 constructor; intro g; refine ⟨disjoint_left.mpr (fun j k l=>?_ ),flock_down S _ _ (subset_insert ..) g⟩; obtain ⟨e,h',t⟩:= mem_biUnion.mp l; exact disjoint_left.mp (g (mem_insert_self ..) (mem_insert_of_mem h') (show i≠e from fun t=>h (t.symm ▸ h'))) k t
 rintro ⟨u,v⟩; intro i hi j hj e; rcases mem_insert.mp hi with rfl|l<;> rcases mem_insert.mp hj with rfl|k; · contradiction
 · exact Disjoint.mono_right (hull_sub S _ _ k) u
 · exact Disjoint.mono_left (hull_sub S _ _ l) u.symm
 exact v l k e
lemma flock_union (P Q:Finset I)(p:Disjoint (hull S P) (hull S Q)): flock S (P∪ Q)↔ flock S P∧flock S Q:=by
 constructor; intro h; exact ⟨flock_down _ _ _ subset_union_left h,flock_down _ _ _ subset_union_right h⟩
 rintro ⟨h,g⟩ i u j v l; rcases mem_union.mp u with a|b<;> rcases mem_union.mp v with c|d; exact h a c l; exact Disjoint.mono (hull_sub _ _ _ a) (hull_sub _ _ _ d) p; exact Disjoint.mono (hull_sub _ _ _ b) (hull_sub _ _ _ c) p.symm; exact g b d l
lemma flock_inj {P:Finset I}{x:I}{y:I}{b:B}(t:flock S P)(p:x∈ P)(q:y∈P)(u:b∈ S x)(v:b∈ S y): x=y:=by by_contra h; exact disjoint_left.mp (t p q h) u v
def trains (V:Finset B):= Finset.univ.filter (fun p=> (hull S p)⊆ V ∧ flock S p)
def sumGas(V:Finset B):=∑ p∈ trains S V, ∏ i∈p,f i
lemma sum_zero (H:∀ i,(S i).Nonempty): sumGas S f ∅=1:=by
 rw [sumGas,sum_eq_single ∅,prod_empty]; · intro i p h; obtain ⟨j,hj⟩:=nonempty_iff_ne_empty.mpr h; exact False.elim (not_nonempty_empty ((H j).mono ((hull_sub S i j hj).trans (mem_filter.mp p).2.1)))
 simp [trains,hull,flock_zero]
private lemma deleted(V:Finset B)(x:B)(p:x∈ V): trains S (V.erase x)= (trains S V).filter (fun i=> x∉ hull S i):=by
 ext i; simp only [trains,mem_filter,mem_univ,true_and]; constructor
 · rintro ⟨h,q⟩; exact ⟨⟨h.trans (erase_subset ..),q⟩,fun v=> notMem_erase _ _ (h v)⟩
 rintro ⟨⟨h,q⟩,g⟩; exact ⟨fun i v=> mem_erase.mpr ⟨(fun e=> g (e ▸ v)),h v⟩,q⟩
lemma sum_del(V:Finset B)(x:B)(p:x∈V): let P:= Finset.univ.filter fun i=> x∈ S i ∧ S i ⊆ V;
                                           sumGas S f V=sumGas S f (V.erase x)+ ∑ i∈ P,f i*sumGas S f (V \ S i):=by
 intro P; let F:= (trains S V).filter (fun i=> x∈ hull S i); unfold sumGas; rw [deleted S _ _ p,add_comm]; apply Eq.trans (sum_filter_add_sum_filter_not (trains S V) (fun i=>x∈ hull S i) _).symm; congr 1 -- tune
 let T(i):= trains S (V \ S i)
 simp_rw [mul_sum]; rw [Finset.sum_sigma']; -- target sum_sigma over P
 let E:= P.sigma T; -- issues nondep
 change (∑ i∈ F,∏ j∈i,f j)=_
 have hx {u:Σ _: I, Finset I} (h:u∈E): x∈ S u.1∧ S u.1⊆ V∧ hull S u.2 ⊆ V\ S u.1∧ flock S u.2:=by
    obtain ⟨p,g⟩:= mem_sigma.mp h; obtain ⟨a,b⟩:= (mem_filter.mp p).2; exact ⟨a,b,(mem_filter.mp g).2⟩
 have hk(i)(h:i∈E): i.1∉ i.2:= fun p=> (mem_sdiff.mp ((hx h).2.2.1 (hull_sub S _ _ p (hx h).1))).2 (hx h).1
 have hl(i)(h:i∈E): flock S (insert i.1 i.2):=(shrinkF S i.1 (hk i h)).2 ⟨Finset.disjoint_left.mpr (fun _ l b=> (mem_sdiff.mp ((hx h).2.2.1 b)).2 l),(hx h).2.2.2⟩
 symm; refine sum_bij (fun i _=> insert i.1 i.2) (fun i h=>?_) (fun i h j g e=>?_) ?_ (fun i h=> (prod_insert (hk i h)).symm)
 · exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,(by rw [hull,biUnion_insert]; exact union_subset (hx h).2.1 ((hx h).2.2.1.trans sdiff_subset)), hl i h⟩,hull_sub S _ _ (mem_insert_self ..) (hx h).1⟩
 · obtain ⟨i,v⟩:=i; obtain ⟨j,u⟩:=j; change insert i v= insert j u at e; replace hk:=hk; have he:=hk ⟨j,u⟩ g
   have hw: i=j:= flock_inj S (hl ⟨i,v⟩ h) (mem_insert_self ..) (e.symm ▸ mem_insert_self j u) (hx h).1 (hx g).1; subst j
   have hv : v=u:=by rw [← erase_insert (hk ⟨i,v⟩ h) (s:=v) (a:=i), e,erase_insert he];
   subst v; rfl
 intro i h; obtain ⟨p,q⟩:=mem_filter.mp h; obtain ⟨a,b⟩:= (mem_filter.mp p).2; obtain ⟨j,v,g⟩:= mem_biUnion.mp q
 have ht:= (erase_subset j i); have hu: hull S (i.erase j) ⊆ V:= (hull_down S _ _ ht).trans a; have hf:Disjoint (S j) (hull S (i.erase j)):= ((shrinkF S j (notMem_erase _ _)).1 ((insert_erase v).symm ▸ b)).1; exact ⟨⟨j,i.erase j⟩, mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_univ _,g,(hull_sub S i j v).trans a⟩, mem_filter.mpr ⟨mem_univ _,(fun k (l:k∈ hull S (i.erase j)) => mem_sdiff.mpr ⟨hu l,fun p=>disjoint_left.mp hf p l⟩),flock_down S _ _ ht b⟩⟩,insert_erase v⟩
lemma del_price (p:Toll S u 1 (1/2))(h:∀ i,‖f i‖ ≤ u i) (V:Finset B)(t:Finset B)(g:t⊆V):
 ‖sumGas S f t‖ ≤ Real.exp ((V \ t).card:ℝ)*‖sumGas S f V‖:=by
 let F:=sumGas S f; change ‖F t‖≤_*‖F V‖
 induction V using Finset.strongInduction generalizing t with
 | H V ih =>
   by_cases e:t=V; subst V; simp
   obtain ⟨x,hx⟩:= show (V\ t).Nonempty from sdiff_nonempty.mpr (fun h=> e (Subset.antisymm g h))
   obtain ⟨s,d⟩:= mem_sdiff.mp hx; let V':=V.erase x; let P:= univ.filter fun i=> x∈ S i ∧ S i⊆ V
   let B₀(i):= f i * F (V\ S i)
   have hp:= erase_ssubset s; have he: F V=F V'+∑ i∈P,B₀ i:=sum_del S f V x s; have ht: t⊆ V':= fun i q=>mem_erase.mpr ⟨(fun e=> d (e ▸ q)),g q⟩
   have hφ(i)(u':i∈P): ‖B₀ i‖ ≤ hit S u 1 x i * ‖F V'‖:=by
      let T':=V \ S i; obtain ⟨a,b⟩:= (mem_filter.mp u').2; have hz:T'⊆V':= fun i (v:i∈T')=> mem_erase.mpr ⟨fun h=> (mem_sdiff.mp v).2 (h.symm ▸ a),(mem_sdiff.mp v).1⟩
      unfold B₀ hit; rw [if_pos a,one_mul,norm_mul]; apply (mul_le_mul_of_nonneg_left (ih V' hp T' hz) (norm_nonneg _)).trans; rw [← mul_assoc,mul_comm ‖_‖]; gcongr; intro k l; by_contra h; exact (mem_sdiff.mp l).2 (mem_sdiff.mpr ⟨mem_of_mem_erase (mem_sdiff.mp l).1,h⟩); exact h i -- tune
   have hf: ‖∑ i∈ P,B₀ i‖ ≤ 1/2*‖F V'‖:= by apply le_trans (norm_sum_le ..); apply le_trans (sum_le_sum hφ); rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (budget_sum (p.pays x) P) (norm_nonneg _)
   have hu: ‖F V'‖ ≤ Real.exp 1 * ‖F V‖:=by
      have hg:= norm_le_add_norm_add (F V') (∑ i∈ P,B₀ i); rw [← he] at hg; have hh: (1:ℝ)+1 ≤ Real.exp 1:= Real.add_one_le_exp _; nlinarith [norm_nonneg (F V)]
   apply (ih _ hp t ht).trans; apply (mul_le_mul_of_nonneg_left hu (Real.exp_pos _).le).trans; rw [←mul_assoc,←Real.exp_add]; have hv: (V \ t).card= (V' \ t).card+1:=by rw [show V' \ t=(V \ t).erase x from ?_,card_erase_of_mem hx]; exact (Nat.sub_add_cancel (card_pos.mpr ⟨x,hx⟩)).symm; ext; simp only [V',mem_sdiff,mem_erase]; tauto
   rw [hv,Nat.cast_add,Nat.cast_one]
theorem held (p:Toll S u 1 (1/2))(h:∀ i,‖f i‖≤u i)(v:∀ i,(S i).Nonempty) : Real.exp (-(Fintype.card B:ℝ)) ≤ ‖sumGas S f univ‖:=by
 have ht:=del_price S f u p h univ ∅ (empty_subset _); rw [sum_zero S f v, norm_one,sdiff_empty,card_univ] at ht; rw [Real.exp_neg,inv_eq_one_div,div_le_iff₀ (Real.exp_pos _),mul_comm]; exact ht
end YM.CF.BProof.Contour

import YM.CF.BPress.Palmer.Basics
/- Transport through multiple optional labeling of vertices; no compatibility included in this file. exact counting. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Palmer
open Function Relation Filter NormedSpace MeasureTheory Finset Lattice RG Grid Branch Ledger
open scoped Topology BigOperators InnerProductSpace Classical
variable {I J K:Type*}[Fintype I][DecidableEq I][Fintype J][DecidableEq J][CommSemiring K]
variable (X:J→I)
def Roles (A:Finset J)(P:Finset I): Prop:= A.image X=P∧Set.InjOn X (A:Set J)
def Assembly (P:Finset I):=univ.filter (fun i:Finset J=>Roles X i P)
def tribe (i:I):= univ.filter (fun j:J=>X j=i)
lemma off_role {S:Finset J}{P:Finset I}{i:I}{j k:J}(h:i∉P)(t:S∈ Assembly X P)(e:j∈tribe X i)(f:k∈S): X k ≠X j:=by intro g; rw [←(mem_filter.mp t).2.1] at h; exact h (mem_image.mpr ⟨k,f,g.trans (mem_filter.mp e).2⟩)
variable {k:J} -- shift up
lemma ride_early (i:I){j:J} {S:Finset I}{P:Finset J}(h:i∉ S)(t:j∈tribe X i)(v:P∈Assembly X S): insert j P∈ Assembly X (insert i S):=by
 refine mem_filter.mpr ⟨mem_univ _,?_,fun a h' b p g=>?_⟩; · rw [image_insert,(mem_filter.mp v).2.1,(mem_filter.mp t).2]
 rcases mem_insert.mp (mem_coe.mp h') with l|l <;> rcases mem_insert.mp (mem_coe.mp p) with K|K; exact l.trans K.symm; exact False.elim (off_role X h v t K (g.symm.trans (congrArg _ l))); exact False.elim (off_role X h v t l (g.trans (congrArg _ K))); exact (mem_filter.mp v).2.2 l K g
lemma ride_height (i:I)(S:Finset I)(p:i∉S)(k:Finset J)(h:k∈Assembly X (insert i S)){j:J}(t:j∈k)(q:X j=i) : k.erase j ∈ Assembly X S:= by
 obtain ⟨a,g⟩:= (mem_filter.mp h).2; apply mem_filter.mpr; refine ⟨mem_univ _,?_ , g.mono (by norm_cast; exact erase_subset ..)⟩; ext x; constructor; · intro v; obtain ⟨y,l,rfl⟩:=mem_image.mp v; have hx:X y∈insert i S:= a ▸ mem_image_of_mem X (mem_of_mem_erase l); exact mem_of_mem_insert_of_ne hx (fun u=>ne_of_mem_erase l (g (mem_of_mem_erase l) t (u.trans q.symm))) -- tune
 intro v; obtain ⟨l,r,rfl⟩:= mem_image.mp (a.symm ▸ mem_insert_of_mem v); refine mem_image_of_mem _ (mem_erase.mpr ⟨?_,r⟩); exact fun x=> p (((congrArg X x).trans q) ▸ v)
lemma blocks (u:Finset J) (P:Finset I)(t:u∈ Assembly X P):u.image X=P:=(mem_filter.mp t).2.1
lemma sorted (f:J→K) (S:Finset I): (∏ i∈ S, ∑ j∈tribe X i, f j)= ∑ A∈ Assembly X S,∏ j∈ A,f j:= by
 induction S using Finset.induction_on with
 | empty=> rw [show Assembly X ∅={∅} from ?_]; simp; ext i; by_cases h:i=∅ <;> simp [Assembly, Roles,h,image_eq_empty]
 | @insert i S l ih=>
    rw [prod_insert l,ih,sum_mul]; simp_rw [mul_sum]; rw [←sum_product' (tribe X i) (Assembly X S)] -- tune prim
    apply sum_bij (fun a _=> insert a.1 a.2)
    · intro a t; obtain ⟨a,b⟩:= mem_product.mp t; exact ride_early X _ l a b
    · rintro ⟨a,b⟩ u ⟨r,v⟩ t g; obtain ⟨u,t'⟩:=mem_product.mp u; obtain ⟨h₁,h₂⟩:=mem_product.mp t
      change insert a b=insert r v at g; have he:a=r:=(mem_insert.mp (g ▸ mem_insert_self a b)).resolve_right (fun e=> off_role X l h₂ h₁ e ((mem_filter.mp u).2.trans ((mem_filter.mp h₁).2.symm)))
      have ht(p:Finset J)(g:p∈ Assembly X S): a∉ p:=fun e=> off_role X l g u e rfl; 
      subst r; refine congrArg (Prod.mk a) (?_); have he:=congrArg (·.erase a) g; simpa only [erase_insert (ht _ t'),erase_insert (ht _ h₂)] using he
    · intro k h; obtain ⟨j,z,hj⟩:= mem_image.mp ((blocks X _ _ h).symm ▸ mem_insert_self ..); refine ⟨(j,k.erase j),mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,hj⟩,ride_height X _ _ l k h z hj⟩,insert_erase z⟩ -- tune
    intro a p; obtain ⟨v,g⟩:= mem_product.mp p; exact (prod_insert (fun t=> off_role X l g v t rfl)).symm
lemma salon (b:J→K)(w:I→K)(v:∀ i, w i= ∑ j∈tribe X i,b j) (s: Finset I) : (∏ i∈s,w i)= ∑ A∈ Assembly X s, ∏ j∈A,b j:=by simp_rw [v]; exact sorted X b s
lemma collectMe (K:Type*)[AddCommMonoid K](f:Finset J→ K): ∑ i:Finset I, (∑ j∈Assembly X i, f j)=∑ j:Finset J with Set.InjOn X (↑(j:Finset J):Set J), f j:=by
 simp_rw [Assembly, Roles, sum_filter]; rw [sum_comm]; apply sum_congr rfl; intro i _; by_cases p:Set.InjOn X (i:Set J) <;> simp only [p,and_true, and_false,if_true,if_false,sum_const_zero,sum_ite_eq,mem_univ,ite_true] -- tune
lemma member_sigma {P:I→Type*}[∀ i,Fintype (P i)] (i:I): tribe (J:=Sigma P) Sigma.fst i=univ.image (Sigma.mk i):=by
 ext ⟨j,k⟩; simp only [tribe,mem_filter,mem_univ,true_and,mem_image,exists_true_left]; constructor; intro e; change j=i at e; subst i; exact ⟨_,rfl⟩; rintro ⟨q,h⟩; exact (congrArg Sigma.fst h).symm
lemma trib_sigma {P:I→Type*}[∀ i,Fintype (P i)](f:Sigma P→K) (i:I) :∑ j∈tribe Sigma.fst i,f j= ∑ t: P i,f ⟨i,t⟩:=by rw [member_sigma i]; exact Finset.sum_image (by intro x a y b e; exact eq_of_heq (Sigma.mk.inj e|>.2))
end YM.CF.BPress.Palmer

import YM.SU5.Lamour.Plume
/-!
# Append with cross Wick
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 210000
noncomputable section
namespace YM.CF.Lamour
open Fock Finset NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra
variable {I n:Type*}[LinearOrder n][Fintype n][LinearOrder I] (C A:I → FC n)(d:I→I→ℂ)
/-- successor from normal shift derivative -/
def flap (Z X:FC n)(q:ℂ):=Z*X-q • (X*Z)
variable {C A d}
lemma flap_f (Z X C A:FC n)(v:ℂ)(p:antiB Z C=v • 1)(e:antiB Z A=0)(w:ℂ): flap Z (puffL w C A X) (-w)=v • X- puffL (-w) C A (flap Z X w):=by
 change flap _ (pressFun w C A X) (-w)=_ - pressFun (-w) C A (flap Z X w); unfold flap pressFun
 have hZ:Z*C=v • 1-C*Z:=eq_sub_of_add_eq p; have hV:A*Z= -(Z*A):=eq_neg_of_add_eq_zero_right e
 rw [neg_smul,mul_add,add_mul,←mul_assoc,hZ,sub_mul,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,Algebra.smul_mul_assoc,one_mul,mul_assoc X,hV]
 simp only [sub_mul,mul_sub,smul_sub,smul_add,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,neg_smul,mul_neg,smul_neg,neg_neg,sub_neg_eq_add,mul_assoc]; abel
variable {i j:I}{T S X R:Finset I}{Z:FC n}
theorem port_law (e:∀ j∈ S,antiB Z (A j)=0)(d:I→ℂ)(p:∀ j∈ S,antiB Z (C j)=d j • 1): flap Z (nest C A S) (signum S)=∑ j∈S,(parity j S*d j) • nest C A (S.erase j):=by
 induction S using induction_on_min with
 | empty=> simp [flap,signum]
 | insert i S h ih=>
    have v:= Flies.out h; rw [nest_f C A h,show signum (insert i S)= -signum S from (by rw [signum,card_insert_of_notMem v,puff_succ]; rfl),flap_f Z _ _ _ (d i) (p _ (by simp)) (e _ (by simp)),ih (fun j tj=> e _ (mem_insert_of_mem tj)) (fun j tj=> p _ (mem_insert_of_mem tj)),map_sum,sum_insert v,parity_hi _ _ _ le_rfl, Flies.free h,one_mul,erase_insert v,sub_eq_add_neg,←sum_neg_distrib]; congr 1
    apply sum_congr rfl; intro j w; rw [map_smul,erase_insert_of_ne (h _ w|>.ne),parity_lo _ _ _ (h _ w) v,nest_f C A (Flies.sub h (erase_subset ..)),neg_mul,neg_smul,show signum (S.erase j)= -signum S from (by rw [signum,signum, ← card_erase_add_one w,puff_succ,neg_neg])]
-- right nest concat
@[simp] lemma nest_o(i:I)(C A:I→FC n):nest C A {i}=C i+A i:=by rw [show ({i}:Finset I)=insert i ∅ from rfl,nest_f (S:=∅) C A (by simp [Flies]),nest_empty]; change pressFun (signum (∅:Finset I)) _ _ _=_; simp [pressFun,signum]
lemma puff_right(S X:Finset I)(e:Disjoint S X)(C A U V:FC n): puffL (signum S) C A U * V=puffL (signum (S∪X)) C A (U*V) + signum S • (U*flap A V (signum X)) := by
 change pressFun (signum S) C A U * V = pressFun (signum (S∪X)) C A (U*V) + _; let Z:= A*V; let S':=signum S; let X':=signum X
 have he: signum (S ∪ X)= S'*X':=by rw [signum,card_union_of_disjoint e,puff_add]; rfl
 unfold pressFun flap; rw [he]; simp only [add_mul,mul_sub,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_sub, mul_assoc,smul_smul]; change _ = C*(U*V)+(signum S*signum X) • (U*(V*A)) + _; abel
abbrev Grass(S X:Finset I):Prop:=∀ i∈ S,Flies i X -- left before right
lemma grass_sub (h:Grass S X)(p:T⊆S)(q:R⊆X): Grass T R:= fun i e=>Flies.sub (h i (p e)) q
lemma grass_freed (h:Grass S X): Disjoint S X:= disjoint_left.mpr fun _ w=>Flies.out (h _ w)
lemma grass_crown (h:Grass S X)(p:i∈S): parity i (S∪X)= parity i S:= by rw [plum_union (grass_freed h),Flies.free (h _ p),mul_one]
lemma grass_slide (h:Grass S X)(p:i∈X): parity i (S∪X)=signum S*parity i X:=by rw [plum_union (grass_freed h)]; unfold parity; rw [filter_true_of_mem (fun j tj=> h j tj i p)]; rfl
variable [Fintype I]{K:Op I}
abbrev Furl (K:Op I)(S:Finset I):Prop:=∀ i∈ S,∀ j∈ S,i < j → K i j=0
lemma wake_free (h:Kᵀ= -K)(v:Furl K S)(C A:I→FC n): wake C A K S=nest C A S:=by
 induction S using Finset.induction_on_min with
 | empty=> simp
 | insert i S q ih=> rw [wake_r h q, ih (fun i p j g=>v i (mem_insert_of_mem p) j (mem_insert_of_mem g)),sum_eq_zero fun j tj=> by rw [v i (by simp) _ (mem_insert_of_mem tj) (q _ tj),mul_zero,zero_smul],add_zero,nest_f C A q]
-- argument order implicit Furl in lower
abbrev Cross (K:Op I)(C A:I→FC n)(S X:Finset I):Prop:=∀ i∈ S,∀ j∈ X, antiB (A i) (C j)=K i j • 1 ∧ antiB (A i) (A j)=0
lemma cross_sub(w:Cross K C A S X)(g:T⊆ S)(h:R⊆X): Cross K C A T R:=fun i ti j tj=> w i (g ti) j (h tj)
lemma furl_sub(e:Furl K S)(h:T⊆ S): Furl K T:=fun i hi j hj=>e i (h hi) j (h hj)
theorem wake_concat (h:Kᵀ= -K)(q:Grass S X)(d:Cross K C A S X)(f:Furl K X): wake C A K (S∪X)=wake C A K S * nest C A X:=by
 induction S using Finset.strongInductionOn generalizing X with
 | _ S ih=>
    by_cases u:S.Nonempty
    · let i:=S.min' u; have hv:i∈S:=min'_mem S u; let T:=S.erase i
      have hl:T⊆ S:=erase_subset ..; have hu:T ⊂ S:=erase_ssubset hv; have hp:Flies i T:=fun j tj=>lt_of_le_of_ne (min'_le _ _ (hl tj)) (mem_erase.mp tj|>.1.symm)
      have hx:S=insert i T:=(insert_erase hv).symm; rw [hx,insert_union,wake_r h (show Flies i (T∪X) from fun j e=>(mem_union.mp e).elim (hp j) (q i hv j)),wake_r h hp, ih T hu (grass_sub q hl subset_rfl) (cross_sub d hl subset_rfl) f]
      have ha:=grass_sub q hl (subset_refl X); have hg:= grass_freed ha; let W:=wake C A K; let N:=nest C A; rw [add_mul,puff_right _ _ hg]; let g:= fun j=>(parity j T*K i j) • W (T.erase j)*N X
      rw [port_law (fun j e=> (d i hv j e).2) (K i) (fun j e=> (d i hv j e).1),sum_union hg,sum_mul,mul_sum,smul_sum,←add_assoc]; -- RHS plus terms order
      rw [add_assoc, add_comm (∑ _∈T,_) (∑ _∈X,_),←add_assoc]; congr 1
      · congr 1; apply sum_congr rfl; intro j w; rw [erase_union_distrib,erase_eq_of_notMem (fun l=>disjoint_left.mp hg l w),ih _ hu (grass_sub q hl (erase_subset ..)) (cross_sub d hl (erase_subset ..)) (furl_sub f (erase_subset ..)),grass_slide ha w, Algebra.mul_smul_comm,smul_smul,mul_assoc]
      apply sum_congr rfl; intro j w; have he: T.erase j ⊆S:= Finset.Subset.trans (erase_subset ..) hl; rw [erase_union_distrib, erase_eq_of_notMem (fun e=> disjoint_left.mp hg w e), ih _ (Finset.ssubset_of_ssubset_of_subset (erase_ssubset w) hl) (grass_sub q he subset_rfl) (cross_sub d he subset_rfl) f, Algebra.smul_mul_assoc,grass_crown ha w]
    simp [not_nonempty_iff_eq_empty.mp u, wake_free h f]
-- check pf full evaluation. Raw product sorted
variable (C A)
def prime(S:Finset I):= ((S.sort (· ≤ ·)).map (C+A)).prod
@[simp] lemma prime_nil: prime C A ∅=1:=by simp [prime]
lemma prime_min (v:Flies i S): prime C A (insert i S)=(C i + A i)*prime C A S:=by rw [prime,sort_insert _ (fun j tj=>(v j tj).le) (Flies.out v), List.map_cons,List.prod_cons]; rfl
lemma prime_last (h:Grass S {i}):prime C A (insert i S)=prime C A S*(C i+A i):=by
 induction S using Finset.induction_on_min with
 | empty=> simp [prime]
 | insert j S g ih=>
    have hl:= h j (mem_insert_self ..) i (mem_singleton_self _)
    rw [insert_comm,prime_min _ _ (show Flies j (insert i S) from fun k t=> (mem_insert.mp t).elim (fun e=> e.symm ▸ hl) (g k)),ih (grass_sub h (subset_insert ..) subset_rfl), prime_min _ _ g,mul_assoc]
theorem full_rip(h:Kᵀ= -K)(d:∀ i∈ S,∀ j∈ S,i < j → antiB (A i) (C j)=K i j • 1 ∧ antiB (A i) (A j)=0): wake C A K S=prime C A S:=by
 induction S using Finset.induction_on_max with
 | empty=> simp
 | insert i S g ih=>
    have hv:Grass S {i}:=fun j tj k tk=> by rw [mem_singleton.mp tk]; exact g _ tj
    rw [prime_last C A hv,show insert i S=S∪ {i} by rw [union_comm]; rfl, wake_concat h hv, nest_o, ih (fun j hj k hk=>d j (mem_insert_of_mem hj) k (mem_insert_of_mem hk))]
    · intro j p k q; rw [mem_singleton.mp q]; exact d _ (mem_insert_of_mem p) _ (mem_insert_self ..) (g _ p)
    intro j p k q e; simp [mem_singleton.mp p, mem_singleton.mp q] at e
end YM.CF.Lamour
#print axioms YM.CF.Lamour.full_rip
#print axioms YM.CF.Lamour.wake_concat

import YM.CF.Fock.PfMinor
/-!
# The wake formula
 For finite normal-ordered words of **unrestricted** creation+annihilation columns, interpolate the cross-pair contractions by any skew kernel K. Keep pfaffian & degree signs for Hadamard price.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 180000
noncomputable section
namespace YM.CF.Lamour
open Fock Finset NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra
variable {I n:Type*}[LinearOrder n][Fintype n][LinearOrder I](C A:I → FC n)
def puff (q:ℕ):ℂ:= (-1)^q
@[simp] lemma puff_zero : puff 0=1:=rfl -- tune
@[simp] lemma puff_succ(q:ℕ):puff (q+1)= -puff q:=by simp [puff,pow_succ]
lemma puff_add (p q:ℕ):puff (p+q)=puff p*puff q:=by unfold puff; rw [pow_add]
@[simp] lemma puff_sq(q:ℕ): puff q*puff q=1:=by simp [puff,←mul_pow]
@[simp] lemma puff_norm(q:ℕ): ‖puff q‖=1:=by simp [puff,norm_pow]
-- pre
abbrev pressFun (q:ℂ)(C A W:FC n):= C*W+ q • (W*A)
def puffL(q:ℂ)(C A:FC n): FC n →ₗ[ℂ] FC n where
 toFun W:=pressFun q C A W
 map_add' X Y:=by rw [pressFun,mul_add,add_mul,smul_add]; unfold pressFun; abel
 map_smul' x W:= by change pressFun q C A (x•W)=x • pressFun q C A W; unfold pressFun; rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc,smul_comm q,smul_add]
abbrev Flies (i:I)(S:Finset I):Prop:= ∀ j∈S,i<j
variable {A C}{i j:I}{T S X R:Finset I}
namespace Flies
lemma sub (h:Flies i S)(q:T⊆S):Flies i T:=fun j p=>h j (q p)
lemma out(h:Flies i S):i∉S:=fun e=>lt_irrefl i (h _ e)
lemma free(h:Flies i S):parity i S=1:=by unfold parity; rw [filter_eq_empty_iff.mpr (fun _ h'=>not_lt.mpr (h _ h').le),card_empty,pow_zero]
end Flies
variable (C A)
def signum (S:Finset I):=puff S.card
def nestL : List I → FC n
 | []=>1
 | i::l=> puffL (puff l.length) (C i) (A i) (nestL l)
def nest(X:Finset I):= nestL C A (X.sort (· ≤ ·))
@[simp] lemma nest_empty:nest C A ∅=1:=by simp [nest,nestL]
-- qualify h.free
lemma nest_f (h:Flies i S): nest C A (insert i S)=puffL (signum S) (C i) (A i) (nest C A S):=by rw [nest,sort_insert, nestL,length_sort]; rfl; exact fun j p=>(h j p).le; exact Flies.out h
omit C A in
lemma plum_union (h:Disjoint T S): parity i (T∪S)= parity i T* parity i S:=by unfold parity; rw [filter_union,card_union_of_disjoint (Disjoint.mono (filter_subset _ _) (filter_subset _ _) h),pow_add]
-- phase contracted first (number unpaired BEFORE contracted)
def bow(D S:Finset I):ℂ:=∏ i∈ D,parity i S
@[simp] lemma bow_empty(S:Finset I):bow (∅:Finset I) S=1:=by simp [bow]
lemma bow_addR (h:Flies i X)(v:i∉S):bow X (insert i S)=signum X*bow X S:=by
 unfold bow signum; rw [prod_congr rfl (g:=fun j=> (-1:ℂ)*parity j S) (fun j hj=> (parity_lo S j i (h j hj) v).trans (neg_one_mul ..).symm),prod_mul_distrib,prod_const]; rfl
lemma bow_addL (h:Flies i X)(v:Flies i S):bow (insert i X) S=bow X S:=by rw [bow,prod_insert (Flies.out h), Flies.free v,one_mul]; rfl
lemma bow_fee (h:X ⊆ T)(e:j∈X): let R:=T \ X; parity j T*bow (X.erase j) R=parity j X * bow X R:=by
 intro R; let d:=bow (X.erase j) R; have ht: bow X R=parity j R*d:=by nth_rw 1 [← insert_erase e]; rw [bow,prod_insert (by simp)]; rfl
 rw [ht]; rw [←show parity j (X∪R)=parity j T by rw [show X ∪ R=T from union_sdiff_of_subset h],plum_union (show Disjoint X R from (disjoint_sdiff))]; rw [mul_assoc]
variable [Fintype I]
variable {K:Op I} (h:Kᵀ= -K)
lemma flair(h:Kᵀ= -K)(h':Flies i S) : pf K (insert i S)= ∑ j∈ S,K i j*(parity j S*pf K (S.erase j)):=by
 have hv := pf_spread K h (insert i S) i (mem_insert_self ..); rwa [parity_hi _ _ i le_rfl,Flies.free h',one_mul,erase_insert (Flies.out h')] at hv
lemma pf_turn(h:Kᵀ= -K)(v:pf K T≠0): signum T=1:=by
 induction T using Finset.strongInductionOn with
 | _ T ih=>
   by_cases u:T.Nonempty
   · let i:=T.min' u; have hv:i∈T:=min'_mem T u; let S:=T.erase i; have ht:T=insert i S:=(insert_erase hv).symm
     have hx:Flies i S:=fun j tj=>lt_of_le_of_ne (min'_le _ _ (mem_of_mem_erase tj)) (mem_erase.mp tj|>.1.symm)
     rw [ht,flair h hx] at v
     obtain ⟨j,w,he⟩:= exists_ne_zero_of_sum_ne_zero v
     have hl:=ih _ (show S.erase j ⊂ T from Finset.ssubset_of_ssubset_of_subset (erase_ssubset w) (erase_subset ..)) (right_ne_zero_of_mul (right_ne_zero_of_mul he))
     unfold signum; rw [show T.card=(S.erase j).card+1+1 by rw [card_erase_add_one w, ht,card_insert_of_notMem (Flies.out hx)]]; rwa [puff_succ,puff_succ,neg_neg]
   simpa [not_nonempty_iff_eq_empty.mp u,signum]
lemma pf_degree (h:Kᵀ= -K)(q:R⊆S)(v:pf K R≠0): signum (S\ R)=signum S:=by
 unfold signum; nth_rw 1 [← one_mul (puff _)]; rw [←pf_turn h v]; change puff _*puff _=_; rw [←puff_add,add_comm,card_sdiff_add_card_eq_card q]
variable (K:Op I)
def stir(T X:Finset I):FC n := (bow X (T \ X)*pf K X) • nest C A (T \ X)
def wake (S:Finset I):=∑ T∈S.powerset, stir C A K S T -- unfolds order args? context C before A? variable declared A C! lean variable order? tune
@[simp] lemma wake_empty:wake C A K ∅=1:=by simp [wake,stir,nest_empty,pf,paired_vac] -- C/A issue
variable {C A K}
lemma wake_mic (h:Kᵀ= -K) (v:Flies i S) (q:X⊆S) :stir C A K (insert i S) X=puffL (signum S) (C i) (A i) (stir C A K S X):=by
 let Y:=S\ X; have he:Flies i Y:= Flies.sub v sdiff_subset; have hx:=Flies.sub v q
 unfold stir; rw [show insert i S \ X =insert i Y by exact insert_sdiff_of_notMem _ (Flies.out hx)] -- tune
 by_cases ℓ:pf K X=0
 · rw [ℓ,mul_zero,mul_zero,zero_smul,zero_smul,map_zero]
 rw [bow_addR hx (Flies.out he), pf_turn h ℓ,one_mul,nest_f C A he] -- tune order
 rw [show signum Y=signum S from pf_degree h q ℓ,map_smul]
lemma erase_tar (w:j∈X): S.erase j \ X.erase j=S\ X:=by
 ext k; by_cases h:k=j<;> simp [h,w]
private lemma prime_pay (h:Kᵀ= -K) (v:Flies i S)(q:X⊆S): stir C A K (insert i S) (insert i X)=∑ j∈X,(parity j S*K i j) • stir C A K (S.erase j) (X.erase j) :=by
 let Y:=S \ X; have he:Flies i X:=Flies.sub v q; have hp:Flies i Y:=Flies.sub v sdiff_subset
 rw [stir,insert_sdiff_insert,sdiff_insert_of_notMem (Flies.out v), flair h he]; change (bow (insert i X) Y*_) • nest C A Y=_; rw [bow_addL he hp,mul_sum,sum_smul]; apply sum_congr rfl; intro j w; rw [stir,erase_tar w,smul_smul]; show _ =_ • nest C A Y; congr 1
 have hx: parity j S * bow (X.erase j) Y=parity j X * bow X Y:= bow_fee q w; calc _ = parity j X*bow X Y*(K i j*pf K (X.erase j)):=by ring
                                                                       _= _ := by rw [←hx]; ring
lemma sum_tag {G:Type*}[AddCommMonoid G](f:Finset I→I→ G)(S:Finset I):∑ X∈ S.powerset,∑ j∈ X,f (X.erase j) j=∑ j∈S, ∑ T∈ (S.erase j).powerset, f T j :=by
 let g (T:Finset I) (j):= if j∈T then f (T.erase j) j else 0
 have hx (X:Finset I)(w:X⊆S):∑ j∈X,f (X.erase j) j=∑ j∈S,g X j:=by
    rw [← sum_subset w (fun _ _ g1=> if_neg g1)]; apply sum_congr rfl; intro i t; exact (if_pos t).symm
 have hv j (e:j∈S): ∑ X∈ S.powerset,g X j= ∑ X∈ (S.erase j).powerset, f X j:= by
    nth_rw 1 [← insert_erase e]; rw [sum_powerset_insert (notMem_erase j S)]; rw [sum_eq_zero,zero_add]; swap
    · intro x q; have hc:j∉x:=(fun e=> notMem_erase j S (mem_powerset.mp q e)); exact if_neg hc
    apply sum_congr rfl; intro x v; have ht:j∉x:=(fun e=> notMem_erase j S (mem_powerset.mp v e)); unfold g; rw [if_pos (mem_insert_self ..),erase_insert ht]
 rw [sum_congr rfl (fun X t=> hx X (mem_powerset.mp t)),sum_comm]; exact sum_congr rfl hv
lemma wake_r (h:Kᵀ= -K)(v:Flies i S) : wake C A K (insert i S)=puffL (signum S) (C i) (A i) (wake C A K S)+∑ j∈ S,(parity j S*K i j) • wake C A K (S.erase j):=by
 unfold wake; rw [sum_powerset_insert (Flies.out v),map_sum]; congr 1
 · apply sum_congr rfl; exact fun x t=> wake_mic h v (mem_powerset.mp t)
 rw [sum_congr rfl (fun x e=> prime_pay (A:=A) (C:=C) h v (mem_powerset.mp e))]; simp_rw [smul_sum]; exact sum_tag (f:=fun T j=> (parity j S*K i j) • stir C A K (S.erase j) T) S
end YM.CF.Lamour
#print axioms YM.CF.Lamour.wake_r

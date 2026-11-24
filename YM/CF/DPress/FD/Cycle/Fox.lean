import YM.CF.DPress.FD.Cycle.Tax
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD.Cycle
open List Filter Set
open scoped Topology BigOperators ENNReal Classical
-- both one-variable extensions of b
local notation "ℙ"=> βP
private lemma work0(k:ℕ): ∀ x:Word,x.length=k→ (∑ i:C,βP (x++[i]))=2*(x.length+2)*βP x ∧ (∑ i:C,βP (i::x))= 2*(x.length+2)* βP x :=by
 induction k with
 |zero=> intro x h; rw [List.length_eq_zero_iff.mp h]; simp only [nil_append,βP,road,tint,length_nil,Nat.cast_zero,Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; norm_num [C]
 |succ i ih=>
    intro x h; have hx:x≠[]:=by intro g; subst x; simp at h
    by_cases v:line x; swap
    · have hp:= free false x v; unfold βP; rw [hp]; constructor <;> rw [mul_zero]
      · exact Finset.sum_eq_zero fun i _=> free _ _ (fun g=>v (proper_left g))
      exact Finset.sum_eq_zero fun i _=>free _ _ (fun g=>v (proper_right (x:=[i]) g))
    have ht : pipe x βP=βP x:=(earn false x v hx).symm; let K:= 2*((i:ℝ)+2); constructor
    · have hv:= delim x [] (ℙ); simp only [πnil,List.append_nil,add_zero] at hv; simp_rw [show ∀ i:C, βP (x++[i])= pipe (x++[i]) βP-tax x.getLast? i (βP x) from (fun i=> (eve x [] i v (by simp [line])).trans (by simp)),Finset.sum_sub_distrib]; rw [hv,tL x _ hx,give x _ (fun y=>K*βP y) (?_:∀ y∈ holes x,(∑ i:C,βP (y++[i]))=K*βP y),coin,ht,h]; swap; · intro y p; have he:y.length=i:=Nat.add_right_cancel (Eq.trans (le_port p) h); simp [K,←he,(ih y he).1]
      unfold K; push_cast; ring
    have hv:= delim [] x (ℙ); simp only [πnil,List.nil_append,zero_add] at hv; simp_rw [show ∀ i:C, βP (i::x)= pipe (i::x) βP-tax x.head? i (βP x) from (fun i=> (eve [] x i (by simp [line]) v).trans (by simp)), Finset.sum_sub_distrib]; rw [hv,tR x _ hx,give x _ (fun y=> K*βP y) (?_:∀ y∈ holes x,(∑ i:C,βP (i::y))=K*βP y),coin,ht,h]; swap; · intro y p; have he:y.length=i:=Nat.add_right_cancel ((le_port p).trans h); simp [K,←he,(ih y he).2]
    unfold K; push_cast; ring
lemma merit (x:Word):(∑ i:C,βP (x++[i]))=2*(x.length+2)*βP x ∧ (∑ i:C,βP (i::x))=2*(x.length+2)*βP x:=work0 _ _ rfl
lemma payC (k:ℕ):∀ x:Word,x.length=k+1→ ∑ i:C,cP (x++[i])= 6*βP x:=by
 induction k with
 |zero=> intro x h; rcases x with -|⟨a,x⟩; simp at h; simp at h; rw [h]; simp_rw [show ∀ i:C, cP ([a]++[i])=βP ([a]++[i]) from fun i=>pair_b _ _]; exact (merit _).1.trans (by norm_num)
 |succ i ih=>
    intro x h; have hz:x ≠ []:=by intro e; simp_all
    by_cases g:line x; swap; · rw [show βP x=0 from free _ _ g,mul_zero]; exact Finset.sum_eq_zero fun j _=> free _ _ (fun t=> g (proper_left (clean_line true t)))
    simp_rw [solve x _ g (show 1<x.length from by omega),Finset.sum_sub_distrib]; have ht:=delim x [] cP; simp only [πnil,append_nil,add_zero] at ht; rw [tL x _ hz,tR x _ hz,ht,give x _ (fun y=>6*βP y) (?_:∀ y∈ holes x,(∑ i:C,cP (y++[i]))=6*βP y),coin,show pipe x βP=βP x from (earn false x g hz).symm]; ring
    intro y p; exact ih y (Nat.add_right_cancel ((le_port p).trans h)) -- extension at path.
lemma payT (x:Word)(v:x≠[]):∑ i:C,cP (x++[i])=6*βP x:=by obtain ⟨k,h⟩:=Nat.exists_eq_succ_of_ne_zero (length_pos_iff.mpr v).ne'; exact payC k x h
end YM.CF.DPress.FD.Cycle

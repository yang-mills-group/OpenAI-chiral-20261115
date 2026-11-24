import YM.CF.DPress.FD.Cycle.Fox
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD.Cycle
open List Filter Set
open scoped Topology BigOperators ENNReal Classical
def ratio(r t:ℕ):= Bank (r+t+1)/Bank r/Bank t
lemma ratio_right(r:ℕ): ratio r 0=2*(r+2):=by unfold ratio; rw [Nat.add_zero,pilot,mul_div_cancel_right₀ _ (pBank _).ne',show Bank 0=1 by norm_num [Bank]]; ring
lemma sym(r t:ℕ):ratio r t=ratio t r:=by unfold ratio; rw [Nat.add_comm r t]; ring
lemma cont(r t:ℕ):ratio (r+1) (t+1)=ratio r (t+1)+ratio (r+1) t:=by
 have hr:0<(Bank r):=pBank r; have ht:=pBank t; have hx:=pBank (r+t+1+1); unfold ratio; rw [pilot r,pilot t,show r+1+(t+1)+1=r+t+1+1+1 by omega,pilot (r+t+1+1),show r+1+t+1=r+t+1+1 by omega,show r+(t+1)+1=r+t+1+1 by omega]; push_cast; field_simp; ring -- tune
lemma good(x y:Word): ∑ i:C,βP (x++i::y)=ratio x.length y.length* βP x* βP y:=by
 suffices m:∀ (k:ℕ)(x y:Word),x.length+y.length=k→ (∑ i:C,βP (x++i::y))=ratio x.length y.length*βP x*βP y from m _ x y rfl
 intro k; induction k using Nat.strong_induction_on with | h k ih=>_
 intro x y h; by_cases v:x=[]; · subst x; rw [sym (length _) (length y),List.length_nil,ratio_right, show βP []=1 from rfl,mul_one]; exact (merit _).2
 by_cases q:y=[]; · subst y; rw [List.length_nil,ratio_right, show βP []=1 from rfl,mul_one]; exact (merit _).1
 by_cases p: line x; swap; · rw [show βP x=0 from free _ _ p,mul_zero,zero_mul]; exact Finset.sum_eq_zero fun i _=>free false _ (fun s=>p (proper_left s))
 by_cases u: line y; swap; · rw [show βP y=0 from free _ _ u,mul_zero]; exact Finset.sum_eq_zero fun i _=>free false _ (fun s=> u (proper_right (x:=[i]) (proper_right (x:=x) s))) -- cons problem
 obtain ⟨a,ax⟩:= Nat.exists_eq_succ_of_ne_zero (length_pos_iff.mpr v|>.ne'); obtain ⟨b,bx⟩:=Nat.exists_eq_succ_of_ne_zero (length_pos_iff.mpr q|>.ne'); let K:= ratio a (b+1) * βP y; let L:= ratio (a+1) b* βP x
 have ht:= delim x y βP; simp_rw [eve x y _ p u,Finset.sum_sub_distrib]; rw [ht,tL _ _ v,tR _ _ q, give x _ (fun i=> K* βP i) (?_:∀ w∈ holes x, ∑ i:C,βP (w++i::y)=K*βP w),give y _ (fun i=> L* βP i) (?_ :∀ w∈holes y,∑ i:C,βP (x++i::w)=L*βP w)]
 · rw [coin,coin,show pipe x βP=βP x from (earn false x p v).symm, show pipe y βP=βP y from (earn false y u q).symm,ax,bx,cont]; unfold K L; ring
 -- order
 · intro w p; have hw:= le_port p; rw [ih (x.length+w.length) (by omega) x w rfl,ax, show w.length=b from by omega]
 intro w p; have hw:= le_port p; rw [ih (w.length+y.length) (by omega) w y rfl,bx,show w.length=a from by omega]; unfold K; ring
abbrev ν(x:Word):ℝ:= βP x/Bank x.length
lemma splitH(x y:Word): ∑ i:C,ν (x++i::y)=ν x*ν y:=by
 unfold ν; simp_rw [length_append,length_cons]; rw [←Finset.sum_div,good,show x.length+(y.length+1)= x.length + y.length+1 from (by omega)]; unfold ratio; field_simp [(pBank x.length).ne',(pBank y.length).ne',(pBank (x.length + y.length +1)).ne']
-- cycle law n>= at omission (n=0,1 vs1); use $wat 0` dummy for n=1. one liberty.K.$
abbrev θ(x:Word):ℝ:= cP x/(6* Bank (x.length-1))
lemma monoH (x:Word)(t:x≠[]): ∑ i:C,θ (x++[i])=ν x:=by
 unfold θ; simp_rw [length_append, List.length_singleton, Nat.add_sub_cancel]; rw [←Finset.sum_div,payT _ t]; unfold ν; field_simp
lemma θsym(x y:Word): θ (x++y)=θ (y++x):=by unfold θ cP; rw [turn,length_append,length_append,Nat.add_comm x.length]
lemma νn : ν []=1:=by norm_num [ν,βP,Bank]
end YM.CF.DPress.FD.Cycle

import YM.CF.DPress.FD.Cycle.Wild
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD.Cycle
open List Filter Set
open scoped Topology BigOperators ENNReal Classical
lemma shine (f:C→Word→ℝ)(x:Word) : ∑ i:C, pipe x (f i)=pipe x (fun x=>∑ i:C,f i x):=by
 unfold pipe; generalize holes x = y; induction y with|nil=>simp|cons h t v=>simp_rw [map_cons,List.sum_cons,Finset.sum_add_distrib,v]
lemma coin (f: Word→ℝ)(x:Word)(e:ℝ): pipe x (fun z=> e*f z)=e*pipe x f:=by unfold pipe; generalize holes x=y; induction y with|nil=>simp| cons h t v=>rw [map_cons,List.sum_cons,map_cons,List.sum_cons,mul_add,v]
abbrev Bank(n:ℕ):ℝ:= (2:ℝ)^n * (Nat.factorial (n+1):ℕ)
lemma pBank(n:ℕ) : 0<Bank n:=by unfold Bank; positivity
lemma pilot(n:ℕ): Bank (n+1)=2*(n+2)*Bank n:=by unfold Bank; rw [Nat.factorial_succ (n+1),pow_succ]; push_cast; ring
@[simp] lemma tint(b:Bool):tall b []=1:= rfl
lemma road(b:Bool)(x:C):tall b [x]=1:=by rw [earn b _ (by cases b<;> simp [clean,circle,line]) (by simp),Cycle.singleton,tint]
lemma pair_b(x y:C): tall true [x,y]=tall false [x,y]:=by
 by_cases h:x=y; subst y; rw [free _ _ (by simp [clean,circle,line]),free _ _ (by simp [clean,circle,line])]
 rw [earn _ _ (by simp [clean,circle,line,h]) (by simp),earn _ _ (by simp [clean,line,h]) (by simp)]; simp [pipe,holes,road]
lemma delim (x y:Word)(f:Word→ℝ): ∑ i:C, pipe (x++i::y) f= pipe x (fun w=>∑ i:C,f (w++i::y))+ 4*f (x++y) + pipe y (fun w=>∑ i:C,f (x++i::w)):=by
 simp_rw [star_pipe,Finset.sum_add_distrib, Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; rw [show (Fintype.card C:ℝ)=4 from by simp [C]]; exact congrArg₂ (·+·) (congrArg (fun X=> X+_) (shine (fun i w=>f (w++i::y)) x)) (shine (fun i w=> f (x++i::w)) y)
private lemma tax0 (x:Option C)(v:ℝ)(p:x≠ none):∑ i:C,tax x i v=2*v:=by
 cases x; contradiction; simp [tax]
lemma tL(x:Word)(v:ℝ)(p:x≠[]):∑ i:C,tax x.getLast? i v=2*v:= tax0 _ _ fun h=> p (getLast?_eq_none_iff.mp h)
lemma tR(x:Word)(v:ℝ)(p:x≠[]):∑ i:C,tax x.head? i v=2*v:= tax0 _ _ fun h=> p (head?_eq_none_iff.mp h)
@[simp] lemma πnil(f:Word→ℝ): pipe [] f=0:=by simp [pipe,holes]
lemma proper_left{x y:Word}(h:line (x++y)):line x:=by
 by_cases p:x=[]; simp [p,line]; by_cases q:y=[]; subst y; simpa only [append_nil] using h; exact (proper _ _ p q|>.1 h).1 -- explicit args
lemma proper_right{x y:Word}(h:line (x++y)):line y:=by
 by_cases p:y=[]; simp [p,line]; by_cases q:x=[]; subst x; exact h; exact (proper _ _ q p|>.1 h).2.2
@[simp] lemma tax_none (b:C)(x:ℝ):tax none b x=0:= by simp [tax]
end YM.CF.DPress.FD.Cycle

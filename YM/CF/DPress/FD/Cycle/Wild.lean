import YM.CF.DPress.FD.Cycle.Build
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD.Cycle
open List Filter Set
open scoped Topology BigOperators ENNReal Classical
lemma rotateP (x y:Word) : pipe (x++y) (tall true) = pipe (y++x) (tall true):=by
 rw [both,both, add_comm (pipe y _) (pipe x (fun w=> tall true (y++w)))]; exact congrArg₂ (·+·) (give _ _ _ (fun w _=> turn w y)) (give _ _ _ (fun w _=> turn x w))
lemma stress (p:Bool) (a:C)(x y:Word):pipe (x++a::a::y) (tall p)=2*tall p (x++a::y):=by
 let Z:=tall p
 have h:pipe x (fun w=>Z (w++a::a::y))=0:= nilP x _ (fun y h=>free _ _ (clean_conflict p)) -- tune
 let t:= a::a::y
 have hv: pipe (a::a::y) (fun w=>Z (x++w))=2*Z (x++a::y):=by
    rw [show a::a::y=[a,a]++y from rfl,both,nilP y (fun w=> Z (x++([a,a]++w))) (fun w _=> free _ _ (clean_conflict p))]; simp [pipe,holes,two_mul] -- rw match lambda
 rw [both]; change pipe _ _+(pipe _ _) = _; rw [h,hv,zero_add]
variable (f:Word→ℝ)
private lemma non0 (p:Bool):∀ n x,0≤ work p n x:=by
 intro n; induction n with
 |zero=> exact fun _=>zero_le_one
 |succ n h=>
    intro x; unfold work; split; next g=> exact List.sum_nonneg (fun a t=>by obtain ⟨w,y,v⟩:=List.mem_map.mp t; exact v ▸ h w)
    next g=> exact le_rfl
lemma tall_nonneg (p:Bool)(x:Word):0≤ tall p x:=non0 p ..
lemma star_pipe (x y:Word)(a:C) : pipe (x++a::y) f= pipe x (fun w=>f (w++a::y))+ f (x++y) + pipe y (fun w=>f (x++a::w)):=by
 rw [both,show a::y=[a]++y from rfl,both, singleton,add_assoc]; rfl
-- conflict alpha indicator charges
abbrev tax (b:Option C)(x:C)(v:ℝ):ℝ := if b = some x then 2*v else 0
abbrev βP(x:Word):= tall false x
abbrev cP(x:Word):= tall true x
private lemma Llast {a:C} (x:Word)(p:x.getLast?=some a): ∃ y,x=y++[a]:=by
 induction x using List.reverseRecOn with
 | nil=> simp at p
 | append_singleton l b h=> exact ⟨l, by rw [show b=a from by simpa using p]⟩
private lemma Rhead {a:C} (x:Word)(p:x.head?=some a): ∃ y,x=a::y:=by cases x; simp at p; simp at p; subst a; exact ⟨_,rfl⟩
variable {X Y:Word} {c:C}
lemma left_s(p:X.getLast?=some c)(y:Word)(b:Bool): ¬ clean b (X++c::y) ∧ pipe (X++c::y) (tall b)=2*tall b (X++y):=by obtain ⟨x,rfl⟩:=Llast X p; rw [List.append_assoc,List.singleton_append,List.append_assoc,List.singleton_append]; exact ⟨clean_conflict b, stress ..⟩
lemma right_s(x:Word)(p:Y.head?=some c)(b: Bool) : ¬ clean b (x++c::Y) ∧ pipe (x++c::Y) (tall b) = 2*tall b (x++Y):=by obtain ⟨y,rfl⟩:=Rhead Y p; exact ⟨clean_conflict b,stress ..⟩
-- cycle special: if at right wildcard conflicts on right edge of circle with first site rotate through right wildcard
lemma right_circle (p:X.head?=some c): ¬clean true (X++[c])∧pipe (X++[c]) cP=2*cP X:=by
 obtain ⟨h,k⟩:= right_s [] p true; simp only [List.nil_append] at h k; refine ⟨fun v=> h ((rot_c X [c]).1 v),?_⟩; rw [show pipe _ cP= _ from rotateP X [c]]; exact k
lemma circular (x:Word)(c:C)(p:line x)(e:x.getLast? ≠ some c)(g:x.head?≠some c):clean true (x++[c]):=by
 by_cases h:x=[]; rw [h]; simp [clean,line,circle]
 constructor; · exact (proper x [c] h (by simp)).2 ⟨p,e,by simp [line]⟩
 intro u; simp_rw [List.getLast?_concat]; cases x; contradiction; exact g -- tune
lemma lineL (x y:Word)(c:C)(p:line x)(t:line y)(e:x.getLast?≠ some c)(g:y.head?≠ some c):clean false (x++c::y):=by
 have hp:line (c::y):=by cases y; simp [line]; exact List.isChain_cons_cons.mpr ⟨fun v=> g (v ▸ rfl),t⟩
 by_cases h:x=[]; subst x; exact hp
 exact (proper x (c::y) h (by simp)).2 ⟨p,e,hp⟩
lemma eve(x y:Word)(c:C)(p:line x)(t:line y):βP (x++c::y)= pipe (x++c::y) βP-tax x.getLast? c (βP (x++y))-tax y.head? c (βP (x++y)):=by
 unfold tax; by_cases u:x.getLast?=some c; swap
 · rw [if_neg u,sub_zero]; by_cases v:y.head?= some c
   · obtain ⟨h,k⟩:= right_s x v false; rw [if_pos v, show pipe _ βP= _ from k,sub_self]; exact free _ _ h -- syntax ellipsis
   rw [if_neg v,sub_zero]; exact earn _ _ (lineL x y c p t u v) (by simp)
 obtain ⟨l,g⟩:= left_s u y false; rw [if_pos u,show pipe (x++c::y) βP= 2*βP (x++y) from g,sub_self,show βP _=0 from free _ _ l]; split; swap; simp
 next v=> obtain ⟨x,rfl⟩:=Llast _ u; obtain ⟨y,rfl⟩:=Rhead _ v; rw [List.append_assoc,List.singleton_append,show βP (x++c::c::y)=0 from free _ _ (clean_conflict false)]; ring
lemma solve(x:Word) (c:C)(p:line x) (f:1<x.length): cP (x++[c])=pipe (x++[c]) cP-tax x.getLast? c (cP x)-tax x.head? c (cP x):=by
 unfold tax; by_cases u:x.getLast?=some c; swap
 · rw [if_neg u,sub_zero]; by_cases v:x.head?=some c; swap; · rw [if_neg v,sub_zero]; exact earn _ _ (circular x c p u v) (by simp)
   obtain ⟨v',t⟩:=right_circle v; rw [if_pos v, t, sub_self]; exact free _ _ v'
 obtain ⟨v,t⟩:=left_s u [] true; rw [List.append_nil] at t; rw [if_pos u,show pipe (x++[c]) cP=2*cP x from t,sub_self,show cP _=0 from free _ _ v]; split; swap; simp
 next q=> have he:cP x=0:=free _ _ (fun v=> (show circle x from v).2 f (q.trans u.symm)); rw [he]; ring
end YM.CF.DPress.FD.Cycle

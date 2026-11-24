import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import YM.CF.BPress.Grid.Cube
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD.Cycle
open List Filter Set
open scoped Topology BigOperators ENNReal Classical
abbrev C := Fin 4
abbrev Word:= List C
/-- proper colorings of cycle, including length 0 and 1 as always proper for defining b. -/
abbrev line(x:Word):Prop:= IsChain (·≠·) x
def circle(x:Word):Prop := line x ∧ (1<x.length→ x.head?≠ x.getLast?)
def clean(A:Bool) := if A then circle else line
lemma clean_line (a:Bool){X:Word}(p:clean a X):line X:=by cases a; exact p; exact (show circle X from p).1
-- line append, check at join.
lemma proper (X Y:Word)(p:X≠[])(q:Y≠[]): line (X++Y)↔ line X∧X.getLast?≠Y.head? ∧ line Y:=by
 induction X using List.reverseRecOn with
 | nil=> contradiction
 | append_singleton X x h=>
    cases Y with
    | nil=> contradiction
    | cons b Y=> unfold line; rw [append_assoc,List.singleton_append,List.isChain_append_cons_cons]; simp
lemma clean_conflict {x y:Word}{b:C}(p:Bool) : ¬ clean p (x++b::b::y):=fun v=>(isChain_append_cons_cons.mp (clean_line p v)).2.1 rfl
lemma rot_c(X Y:Word): circle (X++Y)↔circle (Y++X):=by
 by_cases p:X=[]; simp [p]; by_cases q:Y=[]; simp [q]; unfold circle; have he:1<(X++Y).length:=by have he:= List.length_pos_iff.mpr p; have hy:= List.length_pos_iff.mpr q; rw [length_append]; omega
 have hv:1<(Y++X).length:=by simp only [length_append,Nat.add_comm Y.length]; exact length_append ▸ he
 have hz(Z W:Word)(p:Z≠[]):(Z++W).head?=Z.head?:=by cases Z; contradiction; simp
 have hx(Z W:Word)(p:W≠[]): (Z++W).getLast?=W.getLast?:=by induction W using List.reverseRecOn <;> simp_all [←append_assoc] -- tune
 rw [proper X Y p q,proper Y X q p,hz X Y p,hz Y X q,hx X Y q,hx Y X p, imp_iff_right he, imp_iff_right hv]; grind -- order
-- sum after one deletion
@[simp] def holes : Word→ List Word
| []=> []
| (a::x)=> x:: (holes x).map (fun y=>a::y)
attribute [-simp] holes
def pipe(x:Word)(b:Word→ℝ) := ((holes x).map b).sum
lemma both(x y:Word)(f:Word→ℝ):pipe (x++y) f=pipe x (fun w=>f (w++y))+pipe y (fun w=> f (x++w)):=by
 have he : holes (x++y) = (holes x).map (fun w=>w++y) ++ (holes y).map (fun w=>x++w):=by induction x with|nil=> simp [holes]|cons i x h=> simp [holes,h,List.map_map,List.map_append,Function.comp_def]
 rw [pipe,he]; simp only [pipe,List.map_append,List.map_map,List.sum_append]; rfl
lemma line_tip (x:Word):circle x→ line x:= fun h=>h.1
lemma le_port {x y:Word}(p:y∈holes x):y.length+1=x.length:=by
 induction x generalizing y with
 | nil=> simp [holes] at p
 | cons i x ih=>
    rw [holes,mem_cons,List.mem_map] at p; rcases p with p|⟨a,w,rfl⟩; rw [p]; simp; have hp:= ih w; simp only [length_cons]; omega
lemma give (x:Word)(A B:Word→ℝ)(h:∀ y∈holes x,A y=B y):pipe x A=pipe x B:=congrArg List.sum (List.map_congr_left h)
lemma nilP(x:Word)(A:Word→ℝ)(h:∀ y∈holes x,A y=0):pipe x A=0:=by rw [give x A (fun _=>0) h]; simp [pipe]
lemma singleton(f:Word→ℝ)(c:C): pipe [c] f=f []:=by simp [holes,pipe]
-- linear ψ.Build to given fuel n
noncomputable def work (a:Bool) :ℕ→Word→ℝ
| 0,_=> 1
| n+1,x=> if clean a x then pipe x (work a n) else 0
abbrev tall(a:Bool)(x:Word):=work a x.length x
lemma earn(a:Bool)(x:Word)(p:clean a x)(h:x≠[]): tall a x=pipe x (tall a):=by
 obtain ⟨n,t⟩:=Nat.exists_eq_succ_of_ne_zero (ne_of_gt (length_pos_iff.mpr h)); unfold tall; rw [t,work,if_pos p]; exact give x _ _ fun i v=>by rw [show List.length i=n by have he:= le_port v; omega] -- expand lambda
lemma free(a:Bool)(x:Word)(p:¬ clean a x): tall a x=0:=by
 cases x; · apply False.elim (p (?_)); cases a <;> simp [clean,line,circle] -- tune
 unfold tall; rw [length_cons,work,if_neg p]
lemma turn_cost(n:ℕ)(x y:Word):work true n (x++y)=work true n (y++x):=by
 induction n generalizing x y with
 |zero=>rfl
 |succ i h=>
    by_cases t:circle (x++y); swap; · rw [work,work,if_neg (show ¬ clean true (x++y) from t),if_neg (show ¬ clean true (y++x) from fun v=>t ((rot_c x y).2 v))] -- tune matches clean
    rw [work,work,if_pos (show clean true _ from t),if_pos (show clean true (y++x) from (rot_c x y).1 t),both,both]; rw [add_comm (pipe y _ ) (pipe x (fun w=> work true i (y++w)))]; exact congrArg₂ (·+·) (give _ _ _ (fun w _=> h w y)) (give _ _ _ (fun w _=> h x w))
lemma turn(x y:Word):tall true (x++y)=tall true (y++x):=by unfold tall; rw [length_append,length_append,Nat.add_comm x.length,turn_cost]
end YM.CF.DPress.FD.Cycle

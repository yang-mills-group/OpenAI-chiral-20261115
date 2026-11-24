import YM.CF.DPress.FD.Cycle.Vol
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD.Cycle
open List Filter Set
open scoped Topology BigOperators ENNReal Classical
variable {I:Type*} (P Q : I→ Finset C)
abbrev EmptyP (i:I) : Prop:=P i=Finset.univ
-- enough for joint probabilities. actual separation stronger.
def Far(x:List I):Prop:= x.IsChain (fun i j=>(EmptyP P i ∨ EmptyP Q j)∧(EmptyP Q i ∨EmptyP P j))
abbrev env(x: List I):Prop:=∀ i∈ x, EmptyP P i∨ EmptyP Q i
abbrev SetOS(x: List I):Prop:=∀ i∈ x, EmptyP P i
abbrev joint(i:I):= P i ∩ Q i
section
variable {P Q}
private lemma hear {x y:List I}{R:I→I→Prop}(v:(x++y).IsChain R): x.IsChain R:=by cases y <;> grind [isChain_iff_forall_rel_of_append_cons_cons] -- maybe heavy. replace
private lemma sea {x y:List I}{R:I→I→Prop}(v:(x++y).IsChain R): y.IsChain R:=by induction x with|nil=>exact v|cons i x ih=> exact ih (v.tail)
lemma swap1{b:List I}{c d:I}(p:EmptyP P c)(t:¬ EmptyP Q c)(h:Far P Q (c::b))(v:∀ i∈ b,¬(EmptyP P i∧EmptyP Q i)) (z:d∈b): EmptyP P d:=by
 induction b generalizing c d with
 |nil=>simp at z
 |cons a b ih=> obtain ⟨⟨hq,hv⟩,hs⟩:= List.isChain_cons_cons.mp h; have he:=hv.resolve_left t; rcases List.mem_cons.mp z with q|q; exact q ▸ he; exact ih he (fun p=> v _ (mem_cons_self ..) ⟨he,p⟩) hs (fun i t=>v i (mem_cons_of_mem _ t)) q
lemma matchP {x: List I}(t:env P Q x) (h:Far P Q x)(v:¬ ∃ i∈ x,EmptyP P i∧EmptyP Q i): SetOS P x ∨ SetOS Q x:=by
 cases x with
 |nil=> exact Or.inl fun _ i=>by simp at i
 |cons i x=>
    rcases t i (mem_cons_self ..) with u|u
    · refine Or.inl fun j t=>?_ ; rcases mem_cons.mp t with p|p; rw [p]; exact u; exact swap1 u (fun p=>v ⟨_,mem_cons_self ..,u,p⟩) h (fun i p t=> v ⟨i,mem_cons_of_mem _ p,t⟩) p
    have hz:Far Q P (i::x):= List.IsChain.imp (l:=(i::x)) (fun i j (h:(EmptyP P i ∨ EmptyP Q j)∧ (EmptyP Q i∨EmptyP P j))=>h.symm -- tuning And.symm
    ) h
    refine Or.inr fun j p=>?_ ; rcases mem_cons.mp p with p|p; exact p ▸ u; exact swap1 u (fun p=>v ⟨_,mem_cons_self ..,p,u⟩) hz (fun i p t=>v ⟨i,mem_cons_of_mem _ p,t.2,t.1⟩) p
end
lemma pay_zero(x:List I)(f:Word→ℝ)(h:SetOS P x ∨ SetOS Q x)(p: evalP N x f=1) :evalP (joint P Q) x f= evalP P x f*evalP Q x f:=by
 unfold joint; obtain h|h:= h; rw [eval_e _ Q x (fun i p=> (show _=Q i from by rw [show P i=_ from h i p]; exact Finset.univ_inter _)),eval_e P N x h,p,one_mul]
 rw [eval_e _ P x (fun i p=>(show _=P i from by rw [show Q i=_ from h i p]; exact Finset.inter_univ _)),eval_e Q N x h,p,mul_one]
private lemma naive (k:ℕ): ∀ x: List I,x.length=k → env P Q x → Far P Q x→evalP (joint P Q) x ν=evalP P x ν*evalP Q x ν:=by
 induction k using Nat.strong_induction_on with| h k h=>_
 intro x l t p; by_cases a: ∃ i∈ x,EmptyP P i ∧ EmptyP Q i; swap; exact pay_zero P Q x _ (matchP t p a) (path_zero ..)
 obtain ⟨i,w,f,g⟩:=a; obtain ⟨x,y,rfl⟩:= List.mem_iff_append.mp w
 rw [splitU _ _ _ _ (show joint P Q i=Finset.univ from by unfold joint; rw [f,g,Finset.inter_self]),splitU _ _ _ _ f,splitU _ _ _ _ g,h x.length (by simp at l; omega) x rfl (fun i p=>t i (mem_append_left _ p)) (hear p), h y.length (by simp at l; omega) y rfl (fun j p=> t j (mem_append_right _ (mem_cons_of_mem i p))) (sea (x:=[i]) (sea (x:=x) p))]; ring
lemma price_Line (x:List I)(t: env P Q x)(p:Far P Q x):evalP (joint P Q) x ν=evalP P x ν*evalP Q x ν:= naive P Q _ _ rfl t p
lemma budgets (x:List I)(q:1<x.length)(p:env P Q x)(u:∀ y z:List I,x=y++z → Far P Q (z++y)):evalP (joint P Q) x θ=evalP P x θ*evalP Q x θ:=by
 have h:Far P Q x:=(by simpa using u [] x rfl); by_cases t:∃ i∈ x,EmptyP P i∧EmptyP Q i; swap; exact pay_zero _ _ _ _ (matchP p h t) (cycle_one x q)
 obtain ⟨i,w,v,g⟩:= t; obtain ⟨x,y,rfl⟩:= List.mem_iff_append.mp w
 have hx:y++x≠ []:= by intro k; simp at q; simp_all -- tune
 have hv(M: I→Finset C)(hM:M i=Finset.univ):evalP M (x ++ i::y) θ= evalP M (y++x) ν:= (rotH M x (i::y)).trans ((rotH M [i] (y++x)).trans (spinH M (y++x) hx i hM))
 have he:Far P Q (y++x):= sea (x:=[i]) (u x (i::y) (show x++i::y=x++i::y from rfl)); rw [hv P v,hv Q g,hv _ (show joint P Q i=_ from by unfold joint; rw [v,g,Finset.inter_self])]; exact price_Line P Q _ (fun i v=>p i (by grind)) he
end YM.CF.DPress.FD.Cycle

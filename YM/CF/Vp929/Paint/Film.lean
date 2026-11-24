import YM.CF.Vp929.Paint.Mask
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.VolumeCape.Paint
open Finset Function
open scoped Classical
local notation "ℙ" => Fin 4
abbrev ApartM{I:Type*}(h t:Mask I)(x y:I):Prop:= (clear h x ∨ clear t y) ∧ (clear h y ∨ clear t x)
variable {I:Type*}(h t:Mask I)(X:List I)
lemma poll_one {I:Type*}(h t:Mask I)(X)(f:Bill)(p:∀ i∈X, clear h i):poll (h*t) X f * poll 1 X f=poll h X f * poll t X f:=by rw [poll_agree (h*t) t X f (fun i v=>by simp [Pi.mul_apply,p i v]), poll_agree h 1 _ _ p,mul_comm]
private lemma one_held (p:∀ i∈X,¬ (clear h i ∧ clear t i))(v:∀ i∈X, ApartM h t i i)(k:X.IsChain (ApartM h t)): (∀ i∈X,clear h i) ∨ ∀ i∈X,clear t i :=by
 induction X with
 | nil=> simp
 | cons i x ih=>
   have g(j)(z:j∈x):j∈i::x:= List.mem_cons_of_mem _ z
   have e(a:Mask I)(u:∀ j∈x,clear a j)(v:clear a i) :∀ j∈i::x,clear a j:=by intro j t; cases List.mem_cons.mp t with | inl t => subst j; exact v | inr t => exact u _ t
   let P:=(v i (by simp)).1; rcases ih (fun i z=> p _ (g _ z)) (fun i z=> v _ (g _ z)) k.tail with u|w
   · cases x; exact P.elim (fun p=>Or.inl (by simpa using p)) (fun p=>Or.inr (by simpa using p))
     rename_i j x; exact Or.inl (e h u ((List.isChain_cons_cons.mp k).1.1.resolve_right (fun v=>p j (by simp) ⟨u j (by simp),v⟩)))
   cases x; exact P.elim (fun p=>Or.inl (by simpa using p)) (fun p=>Or.inr (by simpa using p))
   rename_i j x; exact Or.inr (e t w ((List.isChain_cons_cons.mp k).1.2.resolve_left (fun v=>p j (by simp) ⟨v,w j (by simp)⟩)))
abbrev Halves (f:Bill)(h t:Mask I)(X:List I):Prop:= poll (h*t) X f * poll 1 X f=poll h X f * poll t X f
lemma div_line (p:∀ i∈X,ApartM h t i i)(q:X.IsChain (ApartM h t)): Halves (chain X.length) h t X:=by
 generalize E:X.length=N at *; induction N using Nat.strong_induction_on generalizing X with | h n ih =>
 subst n
 by_cases u:∃ i∈X,clear h i∧clear t i
 · obtain ⟨i,u,v,w⟩:=u; obtain ⟨a,b,rfl⟩:= List.append_of_mem u; obtain ⟨c,g,e⟩:= charge a.length b.length
   have u:= ih _ (show a.length < _ from by simp) a (fun i v=> p i (by simp [v])) q.left_of_append rfl; have v':= ih _ (show b.length < _ from by simp; omega) b (fun i v=> p i (by simp [v])) q.right_of_append.tail rfl
   unfold Halves at *; rw [poll_line (h*t) a b i c e (show clear (h*t) _ from by simp [clear, Pi.mul_apply, v,w]), poll_line (1:Mask I) _ _ _ c e rfl,poll_line h _ _ _ c e v,poll_line t _ _ _ c e w]; linear_combination (norm:=ring_nf) c^2*poll (h*t) b (chain b.length)*poll 1 b (chain b.length)*u + c^2*poll h a (chain a.length)*poll t a (chain a.length)*v'
 rcases one_held h t X (fun i p v=> u ⟨i,p,v⟩) p q with v|w; exact poll_one h t X _ v; unfold Halves; rw [mul_comm h t,mul_comm (poll h ..)]; exact poll_one t h X _ w
lemma div_circ(k:ℕ)(e:X.length=k+2)(p:∀ i∈X,ApartM h t i i)(q:∀ x y : List I,X=x++y → (y++x).IsChain (ApartM h t)): Halves (circle k) h t X:=by
 by_cases u:∃ i∈X,clear h i∧clear t i
 · obtain ⟨i,u,v,w⟩:=u; obtain ⟨a,b,rfl⟩:= List.append_of_mem u; let x:=b++a; have E:x.length=k+1:=by simp at *; unfold x; simp; omega
   have H:=div_line h t x (fun i v=> p i (by simpa [x,or_left_comm,or_comm,or_assoc] using by grind)) (q a (i::b) rfl).tail
   have t'(h:Mask I)(p: clear h i): poll h (a++i::b) (circle k)=6*poll h x (chain x.length):=by rw [poll_shift _ _ _ _ (by simpa using e),List.cons_append,poll_erase _ _ _ _ E p,E]
   unfold Halves at *; rw [t' (h*t) (by simp [clear,Pi.mul_apply,v,w]), t' 1 rfl,t' h v,t' t w]; linear_combination 36*H
 rcases one_held h t X (fun i p v=> u ⟨i,p,v⟩) p (by simpa using q [] X (by simp)) with v|w; exact poll_one h t X _ v; unfold Halves; rw [mul_comm h t,mul_comm (poll h ..)]; exact poll_one t h X _ w
end YM.CF.VolumeCape.Paint

import YM.CF.Vp929.Paint.Film
import Mathlib.Data.List.ChainOfFn
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Algebra.Group.Fin.Basic
set_option autoImplicit false
set_option maxHeartbeats 750000
noncomputable section
namespace YM.CF.VolumeCape.Paint
open Finset Function
open scoped Classical
variable {k:ℕ}
local notation "ℙ"=> Fin 4
abbrev RunX(k:ℕ):=Fin (k+2)
local notation "Ξ"=> RunX k
abbrev W(k:ℕ)(x:RunX k→ℙ):ℤ:= circle k (List.ofFn x)
lemma advanceOne(i:Fin (k+1)): i.castSucc+1=i.succ:= by simp
lemma Wshift (x:Ξ→ℙ): W k (fun i=> x (i+1))=W k x := by
 unfold W; nth_rw 2 [List.ofFn_succ]; rw [List.ofFn_succ',circShift] <;> simp
lemma Wtrans (x:Ξ→ℙ)(z:Ξ): W k (fun i=> x (i+z))= W k x:=by
 induction z using Fin.induction with
 | zero=> simp
 | succ i ih=>
   rw [← advanceOne]; convert (Wshift (fun a=> x (a+i.castSucc))).trans ih using 2; funext a; exact congrArg x (by abel)
lemma Wfails (x:Ξ→ℙ)(a:Ξ)(h:x a=x (a+1)): W k x=0:=by
 rw [← Wtrans x a]; let y:Ξ→ℙ:=fun i=> x (i+a); apply circ_zero _ _ (by rw [List.length_ofFn])
 nth_rw 1 [List.ofFn_succ]; simp_rw [List.ofFn_succ]
 intro p; simp only [Fin.succ_zero_eq_one,zero_add,add_comm 1 a,h] at p; exact p [] _ _ rfl
lemma Wnn(x:Ξ→ℙ): 0≤ W k x:= circ_pos _ _ (by rw [List.length_ofFn])
abbrev Rc(k:ℕ): List (RunX k):= List.ofFn _root_.id
private lemma fits(h t: Mask Ξ)(q:∀ i:Ξ,ApartM h t i (i+1)): (Rc k++Rc k).IsChain (ApartM h t):=by
 have H:(Rc k).IsChain (ApartM h t):=List.isChain_ofFn.mpr (fun i v=> by let a:Fin (k+1):=⟨i,by omega⟩; change ApartM h t a.castSucc a.succ; rw [← advanceOne]; exact q _)
 apply H.append H; intro i hI j hJ; unfold Rc at hI hJ; rw [List.ofFn_succ'] at hI; rw [List.ofFn_succ] at hJ; rw [List.concat_eq_append,List.getLast?_concat] at hI; simp at hI hJ; subst i j; simpa using q (Fin.last (k+1))
private lemma poll_rate{I:Type*}(h:Mask I)(n:ℕ)(x:Fin n→I)(f:Bill): poll h (List.ofFn x) f = ∑ y:Fin n→ℙ, f (List.ofFn y)*∏ i:Fin n, h (x i) (y i) :=by
 induction n generalizing f with
 | zero=> simp [poll_nil]
 | succ n ih =>
   let F(y:Fin (n+1)→ℙ):= f (List.ofFn y)*∏ i:Fin (n+1), h (x i) (y i); change _= ∑y,F y
   let E:=Fin.consEquiv (fun _ : Fin (n+1)=>ℙ); rw [← Equiv.sum_comp E F, List.ofFn_succ, poll_cons, Fintype.sum_prod_type]; apply sum_congr rfl; intro i p; rw [ih,mul_sum]; apply sum_congr rfl; intro u t; change _=F (Fin.cons i u); unfold F; rw [Fin.prod_univ_succ,List.ofFn_cons]; simp; ring
lemma Wmask (h:Mask Ξ): ∑x:Ξ→ℙ,W k x*∏i:Ξ,h i (x i)=poll h (Rc k) (circle k) := (poll_rate h _ _ _).symm
lemma Wmass: 0 < ∑x:Ξ→ℙ,W k x:=by have p:=poll_circ (X:=Rc k) (k:=k) (by simp [Rc]); rw [← Wmask] at p; simpa using p
lemma Wsector(h t:Mask Ξ)(p:∀ i:Ξ,ApartM h t i i)(q:∀ i:Ξ,ApartM h t i (i+1)): Halves (circle k) h t (Rc k):=by
 apply div_circ _ _ _ k (by simp [Rc]) (fun i _=> p i); intro x y e; have H:= fits h t q; rw [e] at H; have E:x++y++(x++y)=x++((y++x)++y):= by simp
 rw [E] at H; exact H.right_of_append.left_of_append
end YM.CF.VolumeCape.Paint

import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 520000
noncomputable section
/-! Four-color Holroyd--Liggett line/cycle weight argument. Organization via deletion
    MINUS twice each consecutive-duplicate deletion, making recurrences hold on all words. -/
namespace YM.CF.VolumeCape.Paint
open Finset Function
open scoped Classical
local notation "ℙ" => Fin 4
abbrev Word:= List (Fin 4)
abbrev Bill:= Word→ℤ
def D (f:Bill) : Word→ℤ
| [] => 0
| a::x=> f x + D (fun y=> f (a::y)) x - if x.head?=some a then 2*f x else 0
 termination_by x=>x.length
@[simp] lemma D_nil(f):D f []=0:= D.eq_1 ..
lemma D_cons(f a x): D f (a::x)= f x + D (fun y=> f (a::y)) x - if x.head?=some a then 2*f x else 0:= D.eq_2 ..
lemma D_ext(f g x)(h:∀ y : Word,y.length+1=(x:Word).length→ f y=g y):D f x=D g x:=by
 induction x generalizing f g with
 | nil => simp
 | cons a x ih=> rw [D_cons,D_cons,ih (fun y=> f (a::y)) (fun y=>g (a::y)) (fun y v=>h _ (by simpa)), h x (by simp)]
lemma D_ext'(f g x)(h:∀ z w : Word,∀a:ℙ,x=z++a::w→ f (z++w)=g (z++w)):D f x=D g x:=by
 induction x generalizing f g with
 | nil=>simp
 | cons a x ih=> rw [D_cons,D_cons,ih (fun y=>f (a::y)) (fun y=>g (a::y)) (fun z w i v=>by simpa using h (a::z) w i (by simp [←v])), show f x=g x from by simpa using h [] x a rfl]
lemma D_const(f x)(c:ℤ): D (fun y=> c*f y) x= c* D f x:=by
 induction x generalizing f with
 | nil=> simp
 | cons a x ih=> rw [D_cons, D_cons, ih (fun y=>f (a::y))]; split <;> ring
lemma D_sum{I:Type*}[Fintype I](F:I→Bill)(X:Word): D (fun y=>∑i:I,F i y) X=∑i:I, D (F i) X:=by
 induction X generalizing F with
 | nil=>simp
 | cons i z ih=>rw [D_cons,ih (fun j y=>F j (i::y))]; simp_rw [D_cons]; split <;> simp [Finset.sum_sub_distrib,Finset.sum_add_distrib, *,←Finset.mul_sum]
lemma D_zero (X:Word): D (fun _=> 0) X=0:=by simpa using D_const (fun _=>0) X 0
/-- punctured Leibniz rule. -/
lemma D_append(f:Bill)(x:Word)(a:ℙ)(y:Word): D f (x++a::y) = D (fun z=> f (z++a::y)) x + D (fun z=> f (x++z)) (a::y) - if x.getLast?=some a then 2*f (x++y) else 0:=by
 induction x generalizing f with
 | nil=> simp
 | cons i z ih=> cases z with
    | nil =>
       by_cases h:a=i <;> simp [D_cons,h,eq_comm]
    | cons j z=>
       rw [show (i::j::z)++a::y=i::((j::z)++a::y) from rfl,D_cons, ih (fun x=>f (i::x)),D_cons (fun v=>f (v++_))]; simp <;> ring
abbrev Diverse(X:Word):Prop:=∀ i j : Word,∀ a:ℙ, X ≠ i++a::a::j
lemma D_nonneg(f:Bill)(x:Word)(h:Diverse x)(u:∀ i : Word,i.length+1=x.length→0≤ f i):0 ≤ D f x:=by
 induction x generalizing f with
 | nil => simp
 | cons a x ih =>
   rw [D_cons]; have ht:x.head? ≠ some a:=by rintro p; cases x <;> simp at p; subst p; exact h [] _ _ rfl
   rw [if_neg ht,sub_zero]; exact add_nonneg (u _ rfl) (ih _ (fun i j b p=>h (a::i) j b (by simp [←p])) (fun y v=>u _ (by simpa using v)))
/-- Complete cancellation does not require assuming the word is otherwise proper. -/
lemma D_eq_zero(f:Bill)(x y:Word)(a:ℙ)(h:∀ i j : Word, ∀ b:ℙ, i.length+j.length+1=x.length+y.length → f (i++b::b::j)=0) : D f (x++a::a::y)=0:=by
 rw [D_append,D_cons (fun z=> f (x++z)),D_cons (fun z=> f (x++a::z))]
 have h1 :D (fun z=>f (z++a::a::y)) x=0:= (D_ext _ (fun _=>0) _ fun z v=> h z y a (by omega)).trans (D_zero x)
 have h2:D (fun z=> f (x++a::a::z)) y=0:= (D_ext _ (fun _=>0) _ fun z v=> h x z a (by omega)).trans (D_zero y)
 have s₁(ifP:y.head?=some a): f (x++a::y)=0:=by cases y <;> simp at ifP; subst ifP; apply h; simp <;> omega
 have s₂(ifP:x.getLast?=some a): f (x++a::y)=0:=by obtain ⟨z,rfl⟩:=List.getLast?_eq_some_iff.mp ifP; rw [List.append_assoc]; apply h; simp <;> omega
 simp only [h1,h2,List.head?_cons,↓reduceIte]; split_ifs with p q q <;> first|simp[*]|ring
 ring
end YM.CF.VolumeCape.Paint

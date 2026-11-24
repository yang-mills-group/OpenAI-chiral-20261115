import Mathlib
/-! Uniform finite-bank machinery to certify exact independence. Define Pens which preserve
 the first and second reads on one region, exchange them on the other. No formula in use for
 an approximation to decorrelation. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Regard
open Function Finset Equiv
open scoped BigOperators Classical
variable {I A B U V W E:Type*}
def Matches (A:Finset I)(f g:I→U) := Set.EqOn f g A
namespace Matches
variable {a b:Finset I}{f g h:I→U}
lemma start(f:I→U):Matches a f f:=fun _ _=> rfl
lemma rot(u:Matches a f g):Matches a g f:=Set.EqOn.symm u
lemma endL(u:Matches a f g)(v:Matches a g h):Matches a f h:= Set.EqOn.trans u v
lemma reduce(u:Matches a f g)(p:b⊆a):Matches b f g:= fun _ h=> u (p h)
end Matches
-- two read point
abbrev UnitX (f:A→E)(x:A×A): E×E :=(f x.1,f x.2)
structure PenX (f:A→B)(g:A→U)(E:Perm (A×A)) : Prop where
 left(x): UnitX f (E x)=UnitX f x
 swap(x): UnitX g (E x)=(UnitX g x).swap
def Pieces (X:Set I)(f:A→I→B)(a:A): X→ B:=fun i=> f a i.val
lemma Pieces_eq{a b:A}(X:Finset I)(f:A→I→B): Pieces (↑X) f a=Pieces X f b ↔ Matches X (f a) (f b) :=⟨fun h i v=>congrFun h (⟨i,v⟩ : (↑X:Set I)),fun h=>funext (fun i=> h i.property)⟩
abbrev Pen (a b:Finset I)(f:A→I→U):= ∃ E:Perm (A×A),PenX (Pieces a f) (Pieces b f) E
lemma penMake (f:A→I→U)(a b:Finset I)(E: Perm (A×A)) (h:∀ x,Matches a (f (E x).1) (f x.1)∧ Matches a (f (E x).2) (f x.2)∧ Matches b (f (E x).1) (f x.2)∧ Matches b (f (E x).2) (f x.1)):PenX (Pieces (↑a) f) (Pieces b f) E:= by refine ⟨fun x=> ?_,fun x=> ?_⟩; exact Prod.ext ((Pieces_eq ..).mpr (h x).1) ((Pieces_eq ..).mpr (h x).2.1); exact Prod.ext ((Pieces_eq ..).mpr (h x).2.2.1) ((Pieces_eq ..).mpr (h x).2.2.2)
lemma fromPen{f:A→I→U}{a b:Finset I}{E: Perm (A×A)}(p:PenX (Pieces (↑a) f) (Pieces b f) E) (x:A×A): Matches a (f (E x).1) (f x.1)∧ Matches a (f (E x).2) (f x.2)∧ Matches b (f (E x).1) (f x.2)∧ Matches b (f (E x).2) (f x.1) := ⟨(Pieces_eq ..).mp (congrArg Prod.fst (p.left x)),(Pieces_eq ..).mp (congrArg Prod.snd (p.left x)),(Pieces_eq ..).mp (congrArg Prod.fst (p.swap x)),(Pieces_eq ..).mp (congrArg Prod.snd (p.swap x))⟩
-- powers & weights
variable [Fintype A]
def count(f:A→Prop):ℕ:=∑ x:A,if f x then 1 else 0
lemma count_card(f:A→Prop): count f=Fintype.card {a// f a}:=by rw [Fintype.card_subtype]; unfold count; rw [←Finset.sum_filter (p:=f) (s:=univ) (f:=fun _=> 1)]; simp
lemma count_con(f g:A→Prop)(h:∀ x,f x↔ g x):count f=count g:=congrArg _ (funext (fun i=>propext (h i)))
lemma count_dice [Fintype W](f:A→Prop)(g:W→Prop):count (fun x:A×W=>f x.1∧g x.2)= count f*count g:=by
 unfold count; rw [Fintype.sum_prod_type,sum_mul]; refine sum_congr rfl fun i _=>?_ ; by_cases p:f i <;> simp [p]
abbrev ball (f:A→B)(g:A→U)(x:B)(y:U):ℕ:= count (fun i=> f i=x∧g i=y)
lemma changeBank [Fintype W](f:A→U)(g:W→U)(h:∀ u, count (fun i=> f i=u)=count (fun j=>g j=u)) :∃ σ:A ≃ W,∀ i,g (σ i)=f i:=by
 let e(u:U): {i:A//f i=u} ≃ {j:W//g j=u}:= Fintype.equivOfCardEq (Eq.trans (count_card _).symm ((h u).trans (count_card _))); exact ⟨Equiv.ofFiberEquiv e, ofFiberEquiv_map e⟩
lemma count_pen (f:A→B)(g:A→U)(p:∀ x y x' y', ball f g x y*ball f g x' y'=ball f g x y'*ball f g x' y): ∃ E, PenX f g E:=by
 let X(i:A×A):= (UnitX f i, UnitX g i); let Y(i:A×A):= (UnitX f i,(UnitX g i).swap)
 obtain ⟨σ,h⟩:= changeBank X Y (by
    rintro ⟨⟨x,y⟩, v,w⟩; let U0(k:A)(x:B)(y:U):= f k=x ∧g k=y; apply Eq.trans _ ((p x v y w).trans ?_); swap
    · exact Eq.symm ((count_con _ (fun i=> U0 i.1 x w ∧ U0 i.2 y v) fun i=>by unfold Y UnitX U0; simp; tauto).trans (count_dice (fun i=>U0 i x w) (fun i=>U0 i y v)))
    exact ((count_con _ (fun i=> U0 i.1 x v ∧ U0 i.2 y w) fun i=>by unfold X UnitX U0; simp; tauto).trans (count_dice (fun i=>U0 i x v) (fun i=>U0 i y w))))
 exact ⟨σ,fun i=> congrArg Prod.fst (h i),fun i=>congrArg (Prod.swap ∘ Prod.snd) (h i)⟩
end YM.CF.BProof.Regard

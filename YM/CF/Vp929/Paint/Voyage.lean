import YM.CF.Vp929.Paint.Car
import Mathlib.GroupTheory.QuotientGroup.Basic
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.VolumeCape.Paint
open Finset Function AddSubgroup QuotientAddGroup
open scoped Classical
local notation "ℙ"=> Fin 4
variable {I L:Type*}[AddCommGroup I][Fintype I] [AddCommGroup L][Fintype L][DecidableEq I][DecidableEq L] {k:ℕ}
namespace Voyage
variable (x:I)
private def build(g:AddSubgroup I): (I ⧸ g) × g ≃ I := by
 let D:=mk' g; have H(y:I ⧸ g):D (Quotient.out (s:=leftRel g) y)=y:=Quotient.out_eq y; have h(i:I):D i=0↔ i∈g:= eq_zero_iff i
 let f(z:(I ⧸ g) × g):= Quotient.out z.1+(z.2 : I); have p(z:(I ⧸ g) × g): D (f z)=z.1:=by rw [show D (f z)=D z.1.out+D z.2 from map_add .., (h _).2 z.2.property,H, add_zero]
 refine Equiv.ofBijective f ⟨?_,?_⟩
 · rintro ⟨i,j⟩ ⟨z,a⟩ v; have E:i=z:= (p (i,j)).symm.trans ((congrArg D v).trans (p (z,a))); subst i; exact congrArg (z,·) (Subtype.ext (add_left_cancel v))
 intro y; let z:= y-(D y).out; let t : g:= ⟨z,(h z).1 (by unfold z; rw [map_sub,H, sub_self])⟩; exact ⟨(D y,t),add_sub_cancel _ _⟩
private def equip (H:addOrderOf x=k+2): Car (I ⧸ zmultiples x) I (·+x) k:=by
 let R : RunX k ≃ zmultiples x := (finCongr H.symm).trans (finEquivZMultiples (isOfFinAddOrder_of_finite x))
 let t:= (Equiv.prodCongr (Equiv.refl _) R).trans (build (zmultiples x)); refine ⟨t,fun j a=>?_⟩
 change Quotient.out j+((a+1).val :ℕ) • x = Quotient.out j+a.val • x + x; rw [add_assoc, ←succ_nsmul, Fin.val_add, Fin.val_one]; apply congrArg (Quotient.out j+·); simpa only [H] using mod_addOrderOf_nsmul x (a.val+1)
abbrev allowsU (v:x≠0):addOrderOf x=(addOrderOf x-2)+2:=by have h:=addOrderOf_pos x; have p:addOrderOf x≠1:=mt AddMonoid.addOrderOf_eq_one_iff.mp v; omega
local instance brigade : Fintype (I ⧸ zmultiples x):= Fintype.ofFinite _
abbrev Choices(x:I)(v:x≠0):=equip x (allowsU x v)
def budget (v:x≠0): (I→ℙ)→ℤ:= (Choices x v).carriage
variable (v:x ≠ 0)
lemma varn(i f)(p:f i=f (i+x)):budget x v f=0:= (Choices x v).legal f i p
lemma nonn(f):0≤budget x v f:=(Choices x v).health f
lemma hearty :0< ∑ f, budget x v f := (Choices x v).charge_total
lemma halves(h t:Mask I)(X:∀i,ApartM h t i i)(Y:∀i,ApartM h t i (i+x)):(∑f:I→ℙ,budget x v f*∏i:I,(h*t) i (f i))*(∑f:I→ℙ,budget x v f)=(∑f:I→ℙ,budget x v f*∏i:I,h i (f i))*(∑f:I→ℙ,budget x v f*∏i:I,t i (f i)):=Car.halves (Choices x v) h t X Y
lemma eq_turn(y:L)(w:y ≠ 0)(E:addOrderOf x=addOrderOf y)(e:I ≃ L)(p:∀i,e (i+x)=e i+y)(f:L→ℙ) : budget x v (f∘e)=budget y w f := by
 have H(n m:ℕ)(p₁:addOrderOf x=n+2)(p₂:addOrderOf y=m+2): (equip x p₁).carriage (f∘e)=(equip y p₂).carriage f:=by
   have h:n=m:=by omega
   subst m; apply Car.cTurn; exact p
 exact H _ _ (allowsU x v) (allowsU y w)
end Voyage
end YM.CF.VolumeCape.Paint

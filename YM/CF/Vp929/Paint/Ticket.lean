import YM.CF.Vp929.Paint.Voyage
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
set_option autoImplicit false
set_option maxHeartbeats 560000
noncomputable section
namespace YM.CF.VolumeCape
open Finset Function Paint
open scoped Classical
@[ext] structure Ticket (I:Type*) [Fintype I] where
 bill:I→ℤ
 nn(i):0 ≤ bill i
 pos:0<∑x,bill x
variable {I J A U V:Type*}[Fintype I]
abbrev Cr(P:Prop):ℤ:= @ite _ P (Classical.propDecidable _) 1 0
@[simp] lemma Cr_pos{P:Prop}(p:P):Cr P=1:=if_pos p
@[simp] lemma Cr_neg{P:Prop}(p:¬ P):Cr P=0:=if_neg p
lemma Cr_imp(P Q):Cr (P∧Q)=Cr P*Cr Q:=by by_cases h:P <;> by_cases q:Q <;> simp [*]
lemma Cr_prod(F:I→Prop):Cr (∀i,F i)= ∏i,Cr (F i):=by
 by_cases h:∀i,F i; simp [h]; rw [Cr_neg h]; push Not at h; obtain ⟨i,e⟩:=h; exact (Finset.prod_eq_zero (mem_univ i) (Cr_neg e)).symm
namespace Ticket
variable (p:Ticket I) (X:I→U)(Y:I→V)
def both(h t:I→ℤ) : Prop:= (∑x,p.bill x*(h x*t x))*(∑x,p.bill x)=(∑x,p.bill x*h x)*(∑x,p.bill x*t x)
abbrev Indep : Prop:= ∀ (s:U→ℤ)(t:V→ℤ), both p (s∘X) (t∘Y)
lemma both_l (h:I→ℤ):p.both h 1:=by simp [both]
lemma both_swap(h t:I→ℤ):p.both h t↔p.both t h:=by unfold both; simp_rw [mul_comm (t _),mul_comm (∑x:I,p.bill x*t x)]
variable {X Y}
lemma depend_shr{a:I→U}(p:Ticket I){x:I→A}{y:I→V}(h: ∀ i j, p.bill i ≠ 0→ p.bill j≠0 → a i=a j→ x i=x j)(v:p.Indep a y):p.Indep x y:=by
 intro s t; let Q(i:U):Prop:= ∃ j,a j=i∧p.bill j≠0; let f(i:U):ℤ:=if g:Q i then s (x (Exists.choose g)) else 0; have e(i): p.bill i≠0 → (s∘x) i=(f∘a) i:=by intro w; have q:Q (a i):=⟨i,rfl,w⟩; change _=f (a i); rw [show f (a i)=_ from dif_pos q]; exact congrArg s (h _ _ w q.choose_spec.2 q.choose_spec.1.symm)
 have H:= v f t; unfold both at *; rw [sum_congr (rfl: (univ:Finset I)=_) (g:=fun i=> p.bill i * ((f∘a) i*(t∘y) i)) (fun i _=>by by_cases w:p.bill i=0; simp [w]; rw [e i w]),sum_congr (rfl:(univ:Finset I)=_) (f:=fun i=>p.bill i*((s∘x) i)) (g:=fun i=>p.bill i * (f∘a) i) (fun i _=>by by_cases w:p.bill i=0; simp [w]; rw [e i w])]; exact H
lemma ind_sym(p:Ticket I){x:I→U}{y:I→V}(v:p.Indep x y):p.Indep y x:=fun a b=> (p.both_swap _ _).1 (v b a)
lemma less {U' V':Type*}{a:I→U'}{b:I→V'}(p:Ticket I){x:I→A}{y:I→V}(h:∀i j,p.bill i ≠ 0→p.bill j ≠ 0→ a i=a j→ x i=x j)(k:∀i j,p.bill i ≠0→p.bill j≠0→ b i=b j→ y i=y j)(u:p.Indep a b):p.Indep x y:= p.ind_sym (p.depend_shr k (p.ind_sym (p.depend_shr h u)))
lemma ind_const(x:U)(y:I→V):p.Indep (fun _=>x) y:=by intro s t; unfold both Function.comp; simp_rw [mul_left_comm (p.bill _),←mul_sum,←sum_mul]; ring
lemma both_hi{J:Type*}[Fintype J]{x:I→J}(Y:I→ℤ) (u:∀ j,p.both (fun ω=>Cr (x ω=j)) Y)(F:J→ℤ): p.both (F∘x) Y :=by
    have v(i:J):∑j,F j*Cr (i=j)=F i:= by unfold Cr; classical exact (Finset.sum_eq_single i (fun j _ v=>by simp [Ne.symm v]) (fun p=>by simp at p)).trans (by simp)
    have z(A:I→ℤ):(∑i:I,A i*(F∘x) i) =∑j:J,F j*∑i:I,A i* Cr (x i=j):=by
       simp_rw [Function.comp_apply]; conv_lhs => arg 2; intro i; rw [← v (x i), mul_sum]
       rw [sum_comm]
       refine sum_congr rfl fun j _=>?_ ; rw [mul_sum]; apply sum_congr rfl; intro i _; ring
    unfold both at *; simp_rw [mul_comm ((F∘x) _) (Y _),← mul_assoc (p.bill _) (Y _)]
    rw [z,z,sum_mul,sum_mul]; refine sum_congr rfl fun j _=>?_ ; simp_rw [mul_assoc]; rw [← u j]; congr 2; apply sum_congr rfl; intro i _; ring
lemma dirac [Fintype U][Fintype V](u:∀ (x:U)(y:V), p.both (fun ω=>Cr (X ω=x)) (fun ω=>Cr (Y ω=y))): p.Indep X Y:=by
 intro f g; exact p.both_hi _ (fun i=> (p.both_swap _ _).1 (p.both_hi _ (fun j=> (p.both_swap _ _).1 (u i j)) g)) f
end Ticket
end YM.CF.VolumeCape

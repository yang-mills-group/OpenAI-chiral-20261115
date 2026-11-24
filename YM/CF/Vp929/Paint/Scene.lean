import YM.CF.Vp929.Law.Motion
import YM.CF.Vp929.Paint.Train
import Mathlib.Tactic.Group
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.VolumeCape
open Finset Function Rooms Lattice
open scoped Classical
@[ext] structure Arm where
 dir:Signed
 charge: Bool
namespace Arm
instance :Fintype Arm:= Fintype.ofEquiv (Signed×Bool) (⟨fun v=>⟨v.1,v.2⟩,fun v=>(v.dir,v.charge),fun _=>rfl,fun _=>rfl⟩)
instance : Group Arm where
 one:=⟨1,false⟩
 mul x y:= ⟨x.dir*y.dir,Bool.xor x.charge y.charge⟩
 inv x:= ⟨x.dir⁻¹,x.charge⟩
 mul_assoc _ _ _:= Arm.ext (mul_assoc ..) (Bool.xor_assoc ..)
 mul_one _:= Arm.ext (mul_one _) (Bool.xor_false _)
 one_mul _:= Arm.ext (one_mul _) (Bool.false_xor _)
 inv_mul_cancel _:= Arm.ext (inv_mul_cancel _) (Bool.xor_self _)
end Arm
@[irreducible] def spanR:=Fintype.card Signed
lemma span_pos:0<spanR:= by unfold spanR; exact Fintype.card_pos
namespace Atlas
local notation "N"=> spanR
abbrev Scope(r:ℕ)(a:Cover):Prop:=Range r 0 a
abbrev Zone(r:ℕ):= {x:Cover//Scope r x}
abbrev Jux(r:ℕ):= {x:Zone (N*r)//x.val≠0}
instance(r:ℕ) : Fintype (Zone r):= Set.Finite.fintype <| (Set.finite_Icc (fun _:Axis=>-(r:ℤ)) (fun _=>(r:ℤ))).subset (show {x:Cover|Scope r x}⊆ _ from fun x (v:Scope r x)=> ⟨fun i=>by have h:=v i; simp only [Pi.zero_apply,zero_sub] at h; change -(r:ℤ)≤ x i; omega,fun i=>by have h:=v i; simp only [Pi.zero_apply,zero_sub] at h; change x i ≤ r; omega⟩)

variable {r:ℕ}
lemma art(a b:Cover): Scope r (a-b)↔Range r b a:=by unfold Scope Range; simp only [Pi.zero_apply,Pi.sub_apply,zero_sub,Int.natAbs_neg,neg_sub]
lemma region(s:Signed)(a:Cover)(v:Scope r a):Scope r (s.act a):=by have h:=(March.mk s false 0).range v; simpa [March.slide] using h
def follow(s: Signed)(r:ℕ): Equiv.Perm (Zone r) where
 toFun a:= ⟨s.act a.val,region s _ a.property⟩
 invFun a:= ⟨s⁻¹.act a.val,region s⁻¹ _ a.property⟩
 left_inv a:= Subtype.ext (by exact s.inv_act _)
 right_inv a:= Subtype.ext (by exact s.act_inv _)
@[simp] lemma foll_m(s t:Signed)(x:Zone r):follow (s*t) r x= follow s r (follow t r x):= Subtype.ext <| Signed.act_mul ..
@[simp] lemma foll_v(x:Zone r):follow 1 r x=x:=Subtype.ext <| Signed.act_one ..
def wr(s:Signed)(r:ℕ): Equiv.Perm (Jux r):= Equiv.subtypeEquiv (follow s (N*r)) fun i=>by change _↔ s.act i.val ≠ 0; nth_rw 2 [← s.act_zero]; exact (not_congr s.act_injective.eq_iff).symm
@[simp] lemma wr_m(s t:Signed)(x:Jux r): wr (s*t) r x=wr s r (wr t r x):=Subtype.ext <| foll_m ..
@[simp] lemma wr_v(x:Jux r):wr 1 r x=x:=Subtype.ext <| foll_v ..
local notation "R"=> N*r
structure Scene(r:ℕ) where
 shade : Jux r→Cover→Fin 4
 flag : Cover→Arm
abbrev Patch(r:ℕ):= (Jux r→Zone (N*r)→ Fin 4)× (Zone (N*(N*r))→Arm)
def survey (x:Scene r)(a:Cover) : Patch r:= (fun i p=>x.shade i (a+p.val),fun i=> x.flag (N • a+i.val))
def follows (x:Arm)(a b:Patch r):Prop:= (∀d i,a.1 d i=b.1 (wr x.dir r d) (follow x.dir _ i)) ∧ ∀ i,b.2 (follow x.dir _ i)= x*a.2 i
def mixed (a b:Patch r):Prop:= ∃x,follows x a b
lemma mixed_dir(a:Patch r):mixed a a:= by refine ⟨1,fun x i=> by change _=a.1 (wr 1 r x) (follow 1 _ i); rw [wr_v,foll_v],?_⟩; intro i; rw [one_mul,show (1:Arm).dir=1 from rfl,foll_v]
lemma mixed_rev {a b:Patch r}(h:mixed a b): mixed b a:=by
 obtain ⟨x,u,v⟩:=h; refine ⟨x⁻¹,fun d i=>?_,fun i=>?_⟩; all_goals simp_rw [show x⁻¹.dir = x.dir⁻¹ from rfl]
 · have h:= (u (wr x.dir⁻¹ r d) (follow x.dir⁻¹ R i)).symm; simpa only [← wr_m,←foll_m,mul_inv_cancel,wr_v,foll_v] using h
 have h:= v (follow x.dir⁻¹ _ i); rw [← foll_m,mul_inv_cancel, foll_v] at h; rw [h, inv_mul_cancel_left]
lemma mixed_trans {a b c:Patch r}(h:mixed a b)(t:mixed b c): mixed a c:=by
 obtain ⟨x,u,v⟩:=h; obtain ⟨y,s,w⟩:=t; refine ⟨y*x,fun i d=>?_,fun i=>?_⟩; all_goals simp_rw [show (y*x).dir= y.dir*x.dir from rfl, foll_m]
 · rw [u,s,wr_m]
 rw [w,v,mul_assoc]
def agreeOn(r:ℕ):Setoid (Patch r):= ⟨mixed,⟨mixed_dir,mixed_rev,mixed_trans⟩⟩
instance booth(r:ℕ): Fintype (Quotient (agreeOn r)):= Fintype.ofFinite _
abbrev height(r:ℕ):=Fintype.card (Quotient (agreeOn r))
def code(p:Patch r): Fin (height r):= Fintype.equivFin _ (Quotient.mk (agreeOn r) p)
lemma readInk(a b:Patch r): code a=code b ↔ mixed a b:= by simp only [code,Equiv.apply_eq_iff_eq]; exact ⟨fun i=>Quotient.exact i,fun i=>Quotient.sound i⟩
end Atlas
end YM.CF.VolumeCape

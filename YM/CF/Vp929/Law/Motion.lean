import YM.CF.Vp929.Law.Border
import Mathlib.Algebra.Group.Action.Defs
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.CF.VolumeCape
open Lattice Finset Function Rooms
open scoped Classical
@[ext] structure March where
 step:Signed
 charge:Bool
 endpt: Cover
namespace March
instance: Group March where
 one:= ⟨1,false,0⟩
 mul x y:= ⟨x.step*y.step,Bool.xor x.charge y.charge,x.step.act y.endpt+x.endpt⟩
 inv x:= ⟨x.step⁻¹,x.charge,-(x.step⁻¹.act x.endpt)⟩
 mul_assoc x y z:=by
    change March.mk _ _ _= _; apply March.ext; exact mul_assoc ..; exact Bool.xor_assoc ..
    change (x.step*y.step).act _+_=x.step.act (y.step.act _+_)+_; simp [Signed.act_mul,add_assoc]; rfl
 one_mul x:=by apply March.ext (one_mul _) (by change Bool.xor false _=_; simp) ; change Signed.act 1 _+0=x.endpt; simp
 mul_one x:=by apply March.ext (mul_one _) (by change Bool.xor _ false=_; simp); change x.step.act 0+x.endpt=x.endpt; simp
 inv_mul_cancel x:= March.ext (inv_mul_cancel _) (Bool.xor_self ..) (add_neg_cancel _)
variable (x y:March)
abbrev slide (a:Cover): Cover := x.step.act a+x.endpt
@[simp] theorem live(a): (1:March).slide a=a:=by change Signed.act 1 a+0=a; simp
@[simp] theorem trans(a): (x*y).slide a=x.slide (y.slide a) :=by change (x.step*y.step).act a+_=x.step.act (y.step.act a+_)+_; simp [Signed.act_mul, slide,add_assoc]; rfl
@[simp] theorem left(a):x⁻¹.slide (x.slide a)=a:=by rw [←trans]; simp
@[simp] theorem right(a):x.slide (x⁻¹.slide a)=a:=by rw [←trans]; simp
def equi:Cover ≃ Cover:= ⟨x.slide,x⁻¹.slide,x.left,x.right⟩
theorem range {r:ℕ} {a b:Cover} (t:Range r a b): Range r (x.slide a) (x.slide b):=by
 intro j; obtain ⟨i,rfl⟩:= x.step.perm.surjective j; have he:= t i; simp only [slide,Pi.add_apply,Signed.act_at]; split <;> omega
@[simp] theorem footstep(a:Cover)(i:Axis): x.slide a (x.step.perm i) = (if x.step.flip i then -a i else a i)+x.endpt (x.step.perm i):=by simp [slide]
def reverse(a:Wall):Wall:=⟨-a.b,-a.a,neg_le_neg a.e⟩
def drift(o:ℤ)(a:Wall):Wall:=⟨a.a+o,a.b+o,add_le_add_left a.e _⟩
abbrev swing(x:March)(i:Axis)(t:Wall):=drift (x.endpt (x.step.perm i)) (if x.step.flip i then reverse t else t)
def follow (a:Rooms):Rooms:= fun i=> x.swing (x.step.perm.symm i) (a (x.step.perm.symm i))
def push(x:March)(i:Axis)(v:ℤ):ℤ:= (if x.step.flip i then -v else v)+x.endpt (x.step.perm i)
@[simp] theorem stride(a:Rooms)(i:Axis): x.follow a (x.step.perm i)=x.swing i (a i):=by simp [follow]
private lemma sing(t:ℤ)(i:Axis):x.swing i (Wall.lone t)=Wall.lone (x.push i t):=by unfold swing March.push; split <;> rfl
@[simp] theorem follows(z:Cover): x.follow (here z)= here (x.slide z):=by funext i; obtain ⟨i,rfl⟩:=x.step.perm.surjective i; simp [x.stride,_root_.id,here,sing,March.push]
local notation "I_"=> x.step.perm
@[simp] theorem swing_le(i:Axis)(a b:Wall): x.swing i a ≤ x.swing i b ↔ a ≤ b:=by
 have H(t w:Wall):t≤w↔ w.a ≤ t.a ∧ t.b ≤ w.b:= Iff.rfl; simp only [H,swing, drift]; split <;> simp [reverse] <;> omega
@[simp] theorem swing_win(i:Axis)(a:Wall): (x.swing i a).win ↔ a.win:= by simp only [swing,Wall.win,drift]; split <;> simp [reverse] <;> omega
theorem swing_tips(i:Axis)(a:Wall)(b:ℤ): (x.swing i a).tips (x.push i b) ↔ a.tips b:=by unfold swing March.push; split <;> simp [drift,reverse,Wall.tips,or_comm]
protected theorem tips(a:Rooms)(z:Cover): Corner (x.follow a) (x.slide z) ↔ Corner a z:= by
 have e(i:Axis): (x.follow a (I_ i)).tips (x.slide z (I_ i)) ↔ (a i).tips (z i):=by rw [x.stride,x.footstep]; exact x.swing_tips ..
 constructor; exact fun p i=>(e i).1 (p _); intro p i; obtain ⟨i,rfl⟩:= x.step.perm.surjective i; exact (e i).2 (p _)
theorem stride_le(a b:Rooms): x.follow a ≤ x.follow b ↔ a ≤ b:=by
 have h(i):x.follow a (x.step.perm i) ≤ x.follow b (x.step.perm i) ↔ a i ≤ b i:=by rw [stride,stride,swing_le]
 constructor; exact fun e i=>(h i).1 (e _); intro e i; obtain ⟨i,rfl⟩:=x.step.perm.surjective i; exact (h i).2 (e _)
lemma eq_in{x y:Rooms}(h:∀i :Cover,here i ≤ x↔ here i ≤ y): x=y:=by
 let a:= (h _).1 x.foot_in; let b:=(h _).1 x.head_in; let c:= (h _).2 y.foot_in; let d:=(h _).2 y.head_in; funext i; exact Wall.ext (le_antisymm (Wall.seen (c i)).1 (Wall.seen (a i)).1) (le_antisymm (Wall.seen (b i)).2 (Wall.seen (d i)).2)
@[simp] lemma foll_one (X:Rooms):(1:March).follow X=X:=by apply eq_in; intro i; have e:=stride_le 1 (here i) X; rw [follows,live] at e; exact e
@[simp] lemma foll_mul (X:Rooms):(x*y).follow X=x.follow (y.follow X):=by
 apply eq_in; intro i; obtain ⟨i,rfl⟩:= (x*y).equi.surjective i; change here ((x*y).slide _) ≤_ ↔ here ((x*y).slide _) ≤_; rw [← (x*y).follows,stride_le]; rw [follows, trans, ←follows, stride_le, ← follows, stride_le]
@[simp] lemma foll_left(X:Rooms):x⁻¹.follow (x.follow X)=X:=by rw [←foll_mul]; simp
@[simp] lemma foll_right(X:Rooms):x.follow (x⁻¹.follow X)=X:=by rw [←foll_mul]; simp
abbrev fnQ:Rooms ≃ Rooms:= ⟨x.follow,x⁻¹.follow,x.foll_left,x.foll_right⟩
end March
end YM.CF.VolumeCape

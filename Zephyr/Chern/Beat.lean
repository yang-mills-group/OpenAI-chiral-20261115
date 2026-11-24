import Zephyr.Chern.Cliff
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice Matrix YM.CF


private lemma tSwap (v w x y z:Quint) : tr5 v w x y z = -tr5 w v x y z := by
  have h:=tr5_adjacent (v+w) x y z
  have a:=tr5_adjacent v x y z
  have b:=tr5_adjacent w x y z
  unfold tr5 at *
  simp only [map_add,add_mul,mul_add,Matrix.trace_add] at h
  rw [a,b,zero_add,add_zero] at h
  apply add_eq_zero_iff_eq_neg.mp;rw [add_comm];exact h

private lemma tLeft (v w x y z:Quint) : tr5 v w x y z = -tr5 v x w y z := by
  rw [cycle,tSwap,←cycle]
private lemma tLast (v w x y z:Quint) : tr5 v w x y z = -tr5 v w x z y := by
  rw [cycle,cycle,cycle,tSwap,←cycle,←cycle,←cycle]
private lemma tTurn (v w x y z:Quint) : tr5 v w x y z=tr5 v y z w x := by
  rw [tSwap, tLeft, neg_neg, cycle w, cycle x] -- move v past w x or y z

def leavesC (a b : Quint) := wand a*wand b -wand b * wand a

private lemma tBeat (v w x y z:Quint) :
    (wand v * leavesC w x * leavesC y z).trace = 4*tr5 v w x y z := by
  have e (a b c d) :
      (wand v * wand a * wand b * wand c * wand d).trace= tr5 v a b c d := rfl
  simp only [leavesC,mul_sub,sub_mul,trace_sub,←mul_assoc,e]
  rw [tLeft v x w y z,tLeft v x w z y,tLast v w x z y]
  ring

lemma beats (v w x y z:Quint) :
    (wand v * ((leavesC w x+leavesC y z)*(leavesC w x+leavesC y z))).trace =
    8 * tr5 v w x y z := by
  simp only [add_mul,mul_add,trace_add,←mul_assoc,tBeat]
  rw [tTurn v y z w x,cycle v w x w, tr5_leap, cycle v y z y,tr5_leap]
  ring

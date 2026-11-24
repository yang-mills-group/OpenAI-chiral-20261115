import YM.CF.DPress.Wagon.Ribbon
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Wagon
open Function Filter Lattice RG Wilson MeasureTheory Skye Rush Spire Scree Tulip
open Fock Finset Scroll SU Lat Cube Phase Branch BPress Chess
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator Kronecker YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable {n L:Side}
namespace Race.Ribbon
variable {T:Race n L}(X:Ribbon T)
abbrev mulT(x:ℕ):ℕ:= x*X.b
abbrev Γtime(x:ℕ):ℕ:= X.runB x+X.mulT x
abbrev Frame (X:Ribbon T)(x:ℕ):Prop:= 0<x ∧ X.Γtime x ≤ T.η
-- true combo bit xor class means shift (blank at left).
abbrev aim(a:ℤ)(b:Bool)(x:ℕ):ℤ:= if b then a+ X.mulT x else a
lemma aimL (a:ℤ)(b:Bool)(x:ℕ) : a ≤ X.aim a b x ∧ X.aim a b x+(X.runB x:ℤ) ≤ a+X.Γtime x:=by cases b <;> unfold aim Γtime<;> split_ifs <;> omega
lemma aimτ (a i:ℤ)(b:Bool)(x:ℕ) : X.aim (a+i) b x= X.aim a b x+i:=by unfold aim; split <;> (try rfl); omega
lemma aimb(r a:ℤ)(b:Bool)(x:ℕ):retro r (X.aim a b x+ X.runB x)= X.aim (retro r (a+ X.Γtime x)) (!b) x:=by unfold aim retro Γtime; cases b<;> simp only [Bool.false_eq_true,Bool.not_true,Bool.not_false,ite_false,ite_true] <;> omega
open Credit
lemma runr {a:ℤ}{F:Fixed.Test n}{k:ℕ}(p:X.arc a k F)(h:X.Frame k)(r:ℤ): X.arc (retro r (a+X.runB k)) k (peer (T.wall r) F):=by
 obtain ⟨t,h⟩:= h; unfold Γtime at h; have he:=reverse_P r (X.arc_c p true) ((X.width_P k a true).trans_le (by omega)); rw [X.width_P,List.reverse_replicate] at he; exact X.enter_arc he
variable {k:ℕ}(p:X.Frame k)
def stripe (p:X.Frame k):Style T where
 w:= X.Γtime k
 p:=by have ht:0<X.runB k:= mul_pos p.1 X.pp; unfold Γtime; omega
 V:= X.V^k
 part a b c:= X.arc (X.aim a (b.xor c) k) k
 seed a b c:= Credit.unitP X.full _ false _
 roof := by
    intro a b c F p; have he:=X.aimL a (b.xor c) k; exact (X.arc_t p).weaken (T.lane he.1 he.2) le_rfl
 per :=by
    intro a b c Z; rw [X.aimτ]; exact ⟨fun h=> dark_lift h,fun h=>lift_up h⟩
 fold := by
    intro a b c F t r; rw [show ((!b).xor c) = !(b.xor c) from (by cases b<;>cases c<;>rfl), ←X.aimb]; exact X.runr t p r
lemma pinL(a:ℤ)(b:Bool){U:Fixed.Test n}(h:X.arc a k U): (X.stripe p).part a b b U:=by
 unfold stripe; change X.arc (X.aim _ _ _) k _; rw [Bool.xor_self]; exact h
lemma pinR(a:ℤ)(b:Bool){U:Fixed.Test n}(h:X.arc (a+ X.mulT k) k U): (X.stripe p).part a b (!b) U:=by
 unfold stripe; change X.arc (X.aim _ _ _) k _; rw [show b.xor (!b)=true from (by cases b<;>rfl)]; exact h
lemma straightL{a:ℤ}{b:Bool}{F:Fixed.Test n}(h:(X.stripe p).part a b b F):X.arc a k F:=by unfold stripe at h; change X.arc (X.aim _ _ _) k _ at h; rw [Bool.xor_self] at h; exact h
lemma straightR{a:ℤ}{b:Bool}{F:Fixed.Test n}(h:(X.stripe p).part a b (!b) F):X.arc (a+X.mulT k) k F:=by unfold stripe at h; change X.arc (X.aim _ _ _) k _ at h; rw [show b.xor (!b)=true from (by cases b<;>rfl)] at h; exact h
end Race.Ribbon
end YM.CF.DPress.Wagon

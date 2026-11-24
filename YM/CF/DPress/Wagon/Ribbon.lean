import YM.CF.DPress.Wagon.Board
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
namespace Race
variable {T:Race n L}
namespace Credit
lemma dark_lift {A:Style T}{a:ℤ}{b:Bool}{p:List Bool}{U:Fixed.Test n}(v:Credit A (a+T.η) b p U): Credit A a b p U :=by
 induction p generalizing a b U with
 | nil=> exact nil_p.mpr (nil_p.mp v)
 | cons i g ih=>
    obtain ⟨F,Y,u,t,x⟩:= pick v; rw [x]; exact next ((A.per ..).mp u) (ih (add_right_comm a (T.η:ℤ) _ ▸ t))
end Credit
-- cost store.P parameters.L_B.PST. piece across full slot of P-width. not band.B. consume Bounds all meetings.
structure Ribbon (T:Race n L) where
 P: ℕ
 b:ℕ
 pp:0<P
 hb:0<b
 V:ℝ
 hV:1≤V
namespace Ribbon
open Credit
variable (X:Ribbon T)
def allows(a:ℤ)(b c:Bool)(F:Fixed.Test n):Prop:= IsMark (T.S_ a (a+X.P)) F X.V ∧ (c=false→F=1)
def full : Style T where
 w:= X.P
 p:= X.pp
 V:= X.V
 part := X.allows
 seed a b c:= ⟨(IsMark.one (T.S_ a (a+X.P))).weaken (Finset.Subset.refl _) X.hV, fun _=>rfl⟩
 roof h:=h.1
 per a b c Y:= by unfold allows; rw [add_right_comm (_:ℤ) (_:ℤ) (↑X.P),T.ratio] -- orientation.Transport.O
 fold := by
   intro a b c Y h r; rw [allows,rem_T]; exact ⟨Rem a _ _ h.1,fun p=> by rw [h.2 p]; exact funext fun i=>Fock.theta_one _⟩
local notation "F" => Fixed.Test n
lemma entry(a:ℤ)(b:Bool){U:F}(t:IsMark (T.S_ a (a+X.P)) U X.V): X.full.part a b true U:=⟨t,fun h=> by contradiction⟩
lemma αturn {i:ℤ}{p:List Bool} {a:Bool}{U:F}(c:Credit X.full i a p U) (b:Bool): Credit X.full i b p U :=by induction c generalizing b with|zero i p=> exact zero ..| next t q ih=> exact next t (ih (!b))
lemma homB(a:ℤ)(b:Bool)(i:ℕ) {U:F} (h:Credit X.full a b (List.replicate i false) U): U=1:=by
 induction i generalizing a b U with|zero=> exact nil_p.mp h|succ i ht=> obtain ⟨x,y,k,p,u⟩:= pick (show Credit _ _ _ (false::List.replicate i false) _ from h); rw [u,(show x=1 from k.2 rfl),one_mul]; exact ht _ _ p
-- stripe data from Copy.Start & sup-Cred; values as chronological product.Child attachments.
def arc (a:ℤ)(k:ℕ): F→Prop := Credit X.full a false (List.replicate k true)
lemma enter_arc {a:ℤ}{i:ℕ}{U:F}{v:Bool}(h:Credit X.full a v (List.replicate i true) U): X.arc a i U:= X.αturn h false
lemma arc_c {a:ℤ}{i:ℕ}{U:F}(h:X.arc a i U)(q:Bool): Credit X.full a q (List.replicate i true) U:= X.αturn h q
abbrev runB (i:ℕ):ℕ := i* X.P
lemma width_P (i:ℕ)(a:ℤ)(b:Bool): blockP X.full a (List.replicate i b)=a+(X.runB i:ℤ):=by rw [blockP,List.length_replicate]; rfl
lemma arc_t {a:ℤ}{i:ℕ}{U:F}(h:X.arc a i U): IsMark (T.S_ a (a+(X.runB i))) U (X.V^i):=by
 have hz:= (X.arc_c h false).tag; rw [width_P, List.length_replicate] at hz; exact hz
lemma compound {a:ℤ}{i j:ℕ}{U V:F}(p:X.arc a i U)(t: X.arc (a+(X.runB i)) j V): X.arc a (i+j) (U* V):=by
 unfold arc; rw [List.replicate_add]; refine companion p ?_; rw [X.width_P]; exact X.arc_c t _
lemma escape(a:ℤ)(i:ℕ){U:F}(h:X.arc (a+T.η) i U): X.arc a i U:= dark_lift h
end Ribbon
end Race
end YM.CF.DPress.Wagon

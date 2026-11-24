import YM.CF.DPress.Wagon.Mosaic
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
namespace Race.Credit
variable {T:Race n L}{A:Style T}{a b:ℤ}{c i d:Bool}{V W X F: Fixed.Test n}{s t:List Bool}(r:ℤ)
lemma reverse_P (p:Credit A a c s V)(v:blockP A a s≤a+T.η): Credit A (retro r (blockP A a s)) (turned s.length c) s.reverse (peer (T.wall r) V):=by
 induction p with
 | zero a b=> rw [show peer (T.wall r) 1=1 from funext fun i=> Fock.theta_one _]; exact zero _ _
 | @next a b c X Y U p t ih=>
    let H:=(a+(A.w:ℤ)); let s':= blockP A a (c::U); let k:= retro r s'; have he: s'=blockP A H U:= block_c ..; have ht : blockP A k U.reverse= retro r H:=by unfold k; rw [he]; unfold retro blockP; rw [List.length_reverse]; omega
    have hc:blockP A H U ≤ H+T.η:=by have h':=upper A H U; have hp: H≥a:=(by unfold H; omega); change s'≤_ at v; omega -- tune addition Int
    rw [List.reverse_cons,peer_times _ _ _ _ _ (A.roof p) t.tag le_rfl (he ▸ v)]; refine companion (P:=A) (a:=k) (c:=turned (U.length+1) b) ?_ ?_; · unfold k; rw [he]; exact ih hc -- tune
    rw [ht,List.length_reverse, turned,turn₂]; exact pin (A.fold p r)
lemma lift_up (p:Credit A a c s V):Credit A (a+(T.η:ℤ)) c s V:=by
 induction p with|zero i j=> exact zero _ _| @next a b c X Y U h t ih=> exact .next ((A.per ..).2 h) (show Credit A _ _ _ _ from (Eq.mp (congrArg (fun i:ℤ=> Credit A i (!b) U Y) (add_right_comm a _ _)) ih)) -- inference
-- certified rotation of word through its chosen start. Uses periodic marking not assignment history.
lemma rotate_Q (p:Credit A a c (s++t) X)(u:blockP A a (s++t)=a+(T.η:ℤ))(v:Even (s++t).length): Credit A (blockP A a s) (turned s.length c) (t++s) X:=by
 obtain ⟨F,G,z,h,rfl⟩:= splitC p; rw [tapL] at u; let M:=blockP A a s; rw [(z.tag.commute h.tag (T.own le_rfl u.le)).eq]; refine companion h ?_; rw [u]; have ht:turned t.length (turned s.length c)=c:=by rw [←turn_v, Nat.add_comm,←List.length_append,turn0 v]
 rw [ht]; exact z.lift_up
end Race.Credit
end YM.CF.DPress.Wagon

import YM.CF.BProof.Align.Table
/-! Stretch filled P, empties Q. Formulas and costs of prop-B-Pproj. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Align
open Function Filter Fock Finset Branch
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][DecidableEq I] {A P Q:Op I}{c:ℝ}
structure Board (A P Q:Op I)(c:ℝ): Prop where
 a:IsStarProjection A
 p:IsStarProjection P
 q:IsStarProjection Q
 pq:P*Q=0
 holes:c • P ≤ P*A*P
 dots:c • Q ≤ Q*(1-A)*Q
 nice : 0<c
 bare : c≤1
def wedgeP (A P:Op I):= land P (A*P)
def wedgeQ (A P:Op I):= A-wedgeP A P
def space (P Q: Op I):=1-(P+Q)
namespace Board
variable (b:Board A P Q c)
include b
lemma wall : IsStarProjection (space P Q):=(upCut b.p b.q b.pq).one_sub
lemma qp : Q*P=0:=swapOrth b.p b.q b.pq
lemma pw : P*space P Q=0:=by rw [space,mul_sub,mul_one,mul_add,b.pq,b.p.isIdempotentElem]; abel
lemma qw : Q*space P Q=0:=by rw [space,mul_sub,mul_one,mul_add,b.qp,b.q.isIdempotentElem]; abel
lemma roof : entered P (A*P)=hutch A P:=by rw [entered,hutch,star_mul,b.a.isSelfAdjoint,b.p.isSelfAdjoint, mul_assoc P,←mul_assoc A A,b.a.isIdempotentElem, mul_assoc] -- tune
lemma doorB : c • (1:Op I) ≤ entered P (A*P):= by rw [b.roof]; exact hutch_earn b.p b.holes b.bare
lemma child : Fit P (A*P):= ⟨b.p,by rw [mul_assoc,b.p.isIdempotentElem],active b.nice b.doorB⟩
lemma drawn : IsStarProjection (wedgeP A P):= b.child.landed
lemma tE : (wedgeP A P).trace=P.trace:= b.child.trace
lemma spanP : A*wedgeP A P=wedgeP A P:=by unfold wedgeP land; rw [←mul_assoc,←mul_assoc,b.a.isIdempotentElem]
lemma sailP : wedgeP A P*A=wedgeP A P:= by have ht:=congrArg star b.spanP; rw [star_mul,b.a.isSelfAdjoint,b.drawn.isSelfAdjoint] at ht; exact ht
lemma leaves : IsStarProjection (wedgeQ A P) := subCut b.drawn b.a b.sailP
lemma into : wedgeQ A P ≤ A:=by unfold wedgeQ; exact sub_le_self _ b.drawn.nonneg
lemma spanQ : A*wedgeQ A P=wedgeQ A P:=by rw [wedgeQ,mul_sub,b.a.isIdempotentElem,b.spanP]
lemma sailQ : wedgeQ A P*A=wedgeQ A P:=by rw [wedgeQ,sub_mul,b.a.isIdempotentElem,b.sailP]
lemma shadow : wedgeP A P*P=A*P:=by nth_rw 1 [←b.sailP]; rw [mul_assoc]; exact b.child.keeps
lemma rimRight : wedgeQ A P*P=0:=by rw [wedgeQ,sub_mul,b.shadow,sub_self]
lemma rimLeft : P*wedgeQ A P=0:=swapOrth b.leaves b.p b.rimRight
lemma apartR : wedgeP A P*wedgeQ A P=0:=by rw [wedgeQ,mul_sub,b.sailP,b.drawn.isIdempotentElem,sub_self]
lemma rightZero : wedgeQ A P*wedgeP A P=0:=swapOrth b.drawn b.leaves b.apartR
lemma bins : wedgeP A P+wedgeQ A P=A:=add_sub_cancel ..
lemma loftHole : c • Q ≤ Q*(1-wedgeQ A P)*Q:= by apply b.dots.trans; nth_rw 1 3 [← b.q.isSelfAdjoint.star_eq]; exact star_left_conjugate_le_conjugate (sub_le_sub_left b.into _) Q -- tune
lemma wedgePformed : wedgeP A P=A*P*(entered P (A*P))⁻¹*(P*A):=by rw [wedgeP,land,send,star_mul,b.p.isSelfAdjoint,b.a.isSelfAdjoint,mul_assoc (A*P)]
/-- right inverse into occupied from P. -/
def clip (A P:Op I): Op I:= star (send P (A*P)) -- include warning
lemma clipA : A*clip A P=clip A P:=by rw [clip,send,star_mul,star_star,←mul_assoc,←mul_assoc,b.a.isIdempotentElem]
lemma clipP : P*clip A P=P:=by
 have he:=congrArg star b.child.lays; rw [star_mul,star_mul,b.a.isSelfAdjoint,b.p.isSelfAdjoint] at he; rw [← b.clipA,←mul_assoc] -- tune
 exact he
lemma clipIn : clip A P*P=clip A P:=by have he:=congrArg star b.child.pulls; rw [star_mul,b.p.isSelfAdjoint] at he; exact he
end Board
end YM.CF.BProof.Align

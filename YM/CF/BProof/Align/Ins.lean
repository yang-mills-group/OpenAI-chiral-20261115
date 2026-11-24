import YM.CF.BProof.Align.House
/-! exact PiH endpoint, range formulas for every use of price. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Align
open Function Filter Fock Finset Branch
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][DecidableEq I] [Nonempty I] {A P Q:Op I}{c:ℝ}{x:Ket I}
def entryP (A P Q: Op I) := floorH A P Q 0-P
namespace Board
variable (b: Board A P Q c)
include b
lemma fit0 : Fit A (house A P Q 0):= b.houseFit _ (by simp)
lemma slot0 : house A P Q 0 = P*wedgeP A P + space P Q*wedgeQ A P:=by rw [house]; simp
lemma slotVL: house A P Q 0*wedgeP A P=P*wedgeP A P:=by rw [b.slot0,add_mul,mul_assoc P,mul_assoc (space P Q), b.drawn.isIdempotentElem,b.rightZero,mul_zero,add_zero]
lemma slotVR: house A P Q 0*wedgeQ A P=space P Q*wedgeQ A P:=by rw [b.slot0,add_mul,mul_assoc P,mul_assoc (space P Q), b.apartR,b.leaves.isIdempotentElem,mul_zero,zero_add]
lemma slotL: space P Q*house A P Q 0=space P Q*wedgeQ A P:=by rw [b.on_rim]; simp
lemma slotQ: Q*house A P Q 0=0:=by rw [b.slot0,mul_add,←mul_assoc,←mul_assoc Q,b.qw,b.qp]; simp
lemma slot_clip : house A P Q 0*clip A P = P:=by
 have ht :wedgeP A P*clip A P=clip A P:=by unfold clip send; rw [star_mul,star_star,←mul_assoc]; exact congrArg (·*_ ) b.child.keeps
 rw [← ht,←mul_assoc,b.slotVL,mul_assoc,ht,b.clipP]
lemma slotIn: floorH A P Q 0*P=P:=by nth_rw 2 [←b.slot_clip]; rw [←mul_assoc,floorH,b.fit0.keeps,b.slot_clip] -- tune nth index
lemma slotSide : P*floorH A P Q 0=P:=by have he:=congrArg star b.slotIn; have h:IsStarProjection (floorH A P Q 0):= b.fit0.landed; rwa [star_mul,b.p.isSelfAdjoint,h.isSelfAdjoint] at he
lemma slotForget: Q*floorH A P Q 0=0:=by rw [floorH,land,←mul_assoc,b.slotQ,zero_mul]
lemma PiHp : IsStarProjection (entryP A P Q):=subCut b.p b.fit0.landed b.slotSide
lemma PiHe : P+entryP A P Q=floorH A P Q 0:=add_sub_cancel .. -- check order
lemma offPiH : P *entryP A P Q=0:=by rw [entryP,mul_sub,b.slotSide,b.p.isIdempotentElem,sub_self]
lemma noPiH: Q *entryP A P Q=0:=by rw [entryP,mul_sub,b.slotForget,b.qp,sub_self]
lemma holdsPiH: space P Q* entryP A P Q=entryP A P Q:=by rw [space,sub_mul,one_mul,add_mul,b.offPiH,b.noPiH,zero_add,sub_zero]
lemma fillPiH : entryP A P Q*(space P Q*wedgeQ A P)=space P Q*wedgeQ A P:=by rw [←b.slotVR,entryP,sub_mul,←mul_assoc,floorH,b.fit0.keeps,b.slotVR,←mul_assoc,b.pw,zero_mul,sub_zero]
theorem inPiH (x: Ket I) : acts (entryP A P Q) x=x ↔ ∃ y:Ket I, acts A y=y ∧ acts P y=0 ∧ x=acts (space P Q) y:= by
 constructor
 · intro h; have ht:= b.fit0.landed; let T:= floorH A P Q 0; have he:acts T x=x:=by unfold T; rw [←b.PiHe,act_add,h,show acts P x=0 from (by nth_rw 1 [← h]; rw [← act_mul,b.offPiH,act_zero]),zero_add]
   obtain ⟨y,V,U⟩:= (b.fit0.range x).1 he; refine ⟨acts (wedgeQ A P) y,?_,?_,?_⟩; rw [←act_mul, b.spanQ]; rw [←act_mul,b.rimLeft,act_zero]; rw [←act_mul,←b.slotL,act_mul,←U]; symm; nth_rw 1 [←h]; rw [←act_mul,b.holdsPiH,h]
 rintro ⟨y,V,PY,H⟩; have hy:acts (wedgeQ A P) y=y:=by rw [wedgeQ,act_sub,b.wedgePformed,act_mul,act_mul P,V,PY,map_zero,sub_zero] -- tune
 have hv:x=acts (space P Q*wedgeQ A P) y:= by rw [act_mul, hy]; exact H
 rw [hv,←act_mul,b.fillPiH]
end Board
end YM.CF.BProof.Align

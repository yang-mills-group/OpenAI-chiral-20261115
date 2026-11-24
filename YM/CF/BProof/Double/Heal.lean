import YM.CF.BProof.Double.View
/-! P-presence,Q-absence correlation parking. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Double
open Function Filter Fock Finset Branch Align Wick
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][DecidableEq I][Nonempty I] {A P Q C:Op I}{c r:ℝ} {x:Book I} {y:Ket I}
lemma treatment (b:Board A P Q c)(u:acts A y=y): ∃ z:Ket I, acts A z=z ∧ acts P z=0 ∧ ‖y-z‖≤ c⁻¹*‖acts P y‖:=by
 let W:=Board.clip A P; let v:= acts W (acts P y); refine ⟨y-v,?_,?_,?_⟩; rw [map_sub,u]; unfold v; rw [←act_mul, b.clipA]; rw [map_sub]; unfold v; rw [←act_mul,b.clipP,selfApply b.p,sub_self]; rw [sub_sub_cancel]; exact (actuary W _).trans (mul_le_mul_of_nonneg_right b.clipNorm (norm_nonneg _))
lemma woods (b:Board A P Q c)(h:acts A y=y)(u:acts P y=0): c * ‖y‖≤‖acts (space P Q) y‖:=by
 apply b.gramMil; rw [wedgeQ,act_sub,b.wedgePformed,act_mul,act_mul P,h,u,map_zero,sub_zero]
lemma tow (x:Ket I)(P A:Op I)(v:acts A x=0)(h:IsSelfAdjoint A)(L:Ket I): inner ℂ x (acts A L)=0:=by rw [←act_inner,h.star_eq,v,inner_zero_left]
lemma womb (b:Board A P Q c)(u:acts Q y=0)(e:acts A y=0): acts (entryP A P Q) (acts (space P Q) y)=0:=by
 let L:=space P Q; let T:=entryP A P Q; let g:=acts T (acts L y); have he:= b.PiHp; obtain ⟨v,t,w,H⟩:=(b.inPiH g).1 (selfApply he (acts L y)); have hv: inner ℂ y v=0:=by apply Eq.trans _ (tow y P A e b.a.isSelfAdjoint v); rw [t]
 have hz: inner ℂ (acts L y) g=inner ℂ g g:=by nth_rw 1 [← show acts T g=g from selfApply he (acts L y)]; rw [←act_inner,he.isSelfAdjoint]
 have hk : inner ℂ y (acts L v)=inner ℂ y v:=by unfold L space; rw [act_sub,act_one,act_add,w,zero_add,inner_sub_right,tow y P Q u b.q.isSelfAdjoint,sub_zero]
 change g=0; apply (inner_self_eq_zero (𝕜:=ℂ)).mp; rw [←hz,H]; rw [← show star L=L from b.wall.isSelfAdjoint.star_eq,act_inner,selfApply b.wall v,hk,hv] -- tune
namespace Deck
variable (p:Double.Deck A P Q C c r)
include p
lemma switching : Board (1-cc A) Q P c:=by
 let T:=p.cbP; refine ⟨(ccProj T.a).one_sub,T.q,T.p,T.qp,?_,?_,T.nice,T.bare⟩; · simpa only [cc_rsmul,cc_mul,p.markB,cc_one,cc_sub] using cc_mono T.dots
 rw [sub_sub_cancel]; simpa only [cc_mul,p.markA,cc_rsmul] using cc_mono T.holes
lemma barL : cc (space P Q)=space P Q:=by unfold space; rw [cc_sub,cc_add,p.markA,p.markB,cc_one]
lemma stepdown (u:acts (cc A) y=0)(e:acts Q y=0):c*‖y‖≤‖acts (space P Q) y‖:=by rw [show space P Q=space Q P from congrArg (1-·) (add_comm P Q)]; exact woods p.switching (by rw [act_sub,u,act_one,sub_zero]) e
lemma plant (u:acts (cc A) y=0)(e:acts Q y=0): acts (cc (entryP A P Q)) (acts (space P Q) y)=0:=by
 have he:acts A (pend y)=0:=by rw [← cc_cc A, ←pend_move, u, pend_zero]
 have hx:acts Q (pend y)=0:=by nth_rw 1 [← p.markB]; rw [←pend_move,e,pend_zero]
 have ht:=congrArg pend (womb p.cbP hx he); simp_rw [pend_move,p.barL,pend_p,pend_zero] at ht; exact ht
lemma compression : ‖(1- cc (entryP A P Q))* cc C * entryP A P Q‖≤r:=by
 let T:= entryP A P Q; have he:=p.cbP; have hf: offCut (floorH A P Q 0) C= offCut T C:=by rw [←he.PiHe]; apply Shoot (P:=T) he.p _ (swapOrth he.p he.PiHp he.offPiH) he.PiHp; rw [Align.Twig,p.markA,p.colorA.eq]
 have hx:=p.safety.fare; rw [hf, ←norm_star] at hx; rw [offCut,star_mul,star_mul,(ccProj he.PiHp).one_sub.isSelfAdjoint, he.PiHp.isSelfAdjoint,p.safety.antiF] at hx; rw [neg_mul,mul_neg,norm_neg,←mul_assoc] at hx; exact hx
lemma design (h:acts (entryP A P Q) y=y): (1-r)*‖y‖≤ ‖acts (cc (entryP A P Q)) (acts (cc C) y)‖:=by
 let T:=entryP A P Q; let f:=acts (cc C) y; let V:= cc T; have hp:= ccProj p.cbP.PiHp; have ht: ‖f‖=‖y‖:=act_unit_norm (U:=⟨_,p.barUnit⟩) y; have hg: ‖acts (1-V) f‖ ≤ r*‖y‖:= by
   apply le_trans (b:=‖acts ((1-V)* cc C*T) y‖) _ ((actuary ..).trans (mul_le_mul_of_nonneg_right p.compression (norm_nonneg _))); rw [act_mul, act_mul, h]
 have hx: ‖f‖ ≤ ‖acts V f‖+‖acts (1-V) f‖:= by apply le_trans _ (norm_add_le ..); rw [←act_add,add_sub_cancel,act_one]
 change _ ≤‖acts V f‖; linarith only [ht,hx,hg]
end Deck
end YM.CF.BProof.Double

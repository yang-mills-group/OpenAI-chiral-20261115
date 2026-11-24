import YM.CF.BProof.Double.Repaint
/-! Left annihilating spaces. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Double
open Function Filter Fock Finset Branch Align Wick
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][DecidableEq I] [Nonempty I] {A P Q C:Op I}{c r:ℝ} {x:Book I}
def Enter(x:Book I)(A:Op I):Prop:= acts A (rows x)= rows x ∧ acts (cc A) (cols x)=0
def Live (x:Book I)(P Q C:Op I):Prop:= let L:=space P Q; acts P (rows x)=0 ∧ acts Q (cols x)=0 ∧ acts L (cols x)=acts (cc C) (acts L (rows x))
theorem realEnter (x:Book I)(A:Op I): Enter x A ↔ acts (penR A) x=x:=by
 constructor; intro ⟨h,g⟩; apply book_ext; simp [penR,h]; simp [penR,g,act_sub]
 intro h; have hz:=congrArg rows h; have ht:=congrArg cols h; simp only [penR,mead,bio,act_zero,zero_add,add_zero,act_sub,act_one] at *; exact ⟨hz,sub_eq_self.mp ht⟩ -- tune
namespace Deck
variable (p: Double.Deck A P Q C c r)
include p
lemma coffin (x:Book I): Live (acts (penL P Q C) x) P Q C :=by
 let S:= camp P Q; let L:= space P Q; let Y:=cc C; have hc:L*S=S:=by unfold L S camp; rw [Algebra.mul_smul_comm,p.cbP.wall.isIdempotentElem.eq]
 have hP: P*S=0:=by unfold S camp; rw [Algebra.mul_smul_comm,p.cbP.pw,smul_zero]
 have hQ: Q*S=0:=by unfold S camp; rw [Algebra.mul_smul_comm,p.cbP.qw,smul_zero]
 let u:= acts (Q+S) (rows x)+acts (S*star Y) (cols x); let v:=acts (Y*S) (rows x)+acts (P+S) (cols x)
 have hz:L*P=0:= swapOrth p.cbP.p p.cbP.wall p.cbP.pw; have ht:L*Q=0:=swapOrth p.cbP.q p.cbP.wall p.cbP.qw
 have hu : acts P u=0:=by unfold u; rw [map_add,← act_mul,←act_mul,mul_add,p.cbP.pq,hP,←mul_assoc P S,hP,zero_mul,zero_add,act_zero, act_zero,add_zero]
 have hv:acts Q v=0:=by unfold v; rw [map_add,←act_mul,←act_mul,←mul_assoc Q Y, ←show Y*Q=Q*Y from p.paneQ,mul_assoc Y,hQ,mul_zero,mul_add Q,p.cbP.qp,hQ,zero_add,act_zero,act_zero,add_zero]
 have hf : acts L v=acts Y (acts L u):=by
    have hl:L*(Y*S)=Y*S:=by rw [← mul_assoc L Y, ←show Y*L=L*Y from p.paneL,mul_assoc Y,hc]; -- tune
    have h1:L*(Q+S)=S:=by rw [mul_add,ht,hc,zero_add]
    have he:Y*(L*(S*star Y))=S:=by rw [←mul_assoc L S,hc,←mul_assoc Y,←p.paneZ.eq, mul_assoc (camp _ _), show cc C *star Y=1 from p.barUnit.2,mul_one]
    unfold v u; rw [map_add,←act_mul L,hl,←act_mul L,mul_add,hz,hc,zero_add,map_add (acts L),map_add (acts Y), ←act_mul L,h1,←act_mul L,←act_mul Y,←act_mul Y,he]
 unfold Live; rw [penL,bio,mead]; exact ⟨hu,hv,hf⟩
lemma rowIn (h:Live x P Q C) : rows (acts (penL P Q C) x)=rows x:=by
 obtain ⟨hp,hq,W⟩:=h; let L:=space P Q; let S:=camp P Q; let t:=rows x; let y:=cols x; let Y:=cc C; have hy:star Y*L=L*star Y:= p.paneS
 have he:L * star Y=star Y* L:=hy.symm; have ht:S* star Y= (1/2:ℂ) • (star Y *L):=by unfold S camp; rw [Algebra.smul_mul_assoc, he]
 have hx: acts (S*star Y) y=acts S t:= by rw [ht,act_smul,act_mul,W, ←act_mul (star Y),show star Y*Y=1 from p.barUnit.1,act_one]; unfold S camp; rw [act_smul] -- tune
 rw [penL,bio,hx,act_add]; change acts Q t+acts S t+acts S t=t; unfold S camp; rw [act_smul,space,act_sub,act_one,act_add,hp]; abel_nf; module
lemma colIn (h:Live x P Q C) : cols (acts (penL P Q C) x)=cols x:=by
 obtain ⟨hp,hq,W⟩:=h; let L:=space P Q; let S:=camp P Q; let Y:=cc C; have he:Y*S=(1/2:ℂ) • (Y*L):= by unfold S camp; rw [Algebra.mul_smul_comm]
 have ht: acts (Y*S) (rows x)=acts S (cols x):=by rw [he,act_smul,act_mul,←W]; unfold S camp; rw [act_smul]
 rw [penL,mead,ht,act_add]; unfold S camp; rw [act_smul,space,act_sub,act_one,act_add,hq]; module
lemma onFoot (x : Book I): Live x P Q C ↔ acts (penL P Q C) x=x:=by refine ⟨fun h=> book_ext (p.rowIn h) (p.colIn h),fun h=>?_⟩; rw [←h]; exact p.coffin x
lemma project : IsStarProjection (penL P Q C):=by
 let U:= penL P Q C; refine ⟨op_columns (fun i=>?_),?_⟩; · rw [act_mul]; exact (p.onFoot (acts U (basisKet i))).mp (p.coffin _)
 unfold IsSelfAdjoint penL; rw [bill_star,star_add,star_add,star_mul,star_mul,p.cbP.p.isSelfAdjoint,p.cbP.q.isSelfAdjoint,p.wall_c,star_star]
end Deck
end YM.CF.BProof.Double

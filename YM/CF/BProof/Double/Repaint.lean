import YM.CF.BProof.Double.Pact
import YM.CF.BProof.Wick.Cliff

/-! Double oriented one-particle projectors. `Deck` requires P,Q real (compare
slots in Single), not A. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Double
open Function Filter Fock Finset Branch Align Wick
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][DecidableEq I] [Nonempty I] {A P Q C:Op I}{c r:ℝ} {U V W: M I}
structure Deck (A P Q C:Op I)(c r:ℝ): Prop where
 cbP: Board A P Q c
 markA : cc P=P
 markB : cc Q=Q
 colorA: Commute C P
 colorB: Commute C Q
 safety : Shelf (floorH A P Q 0) C r
def slip (I:Type*) [Fintype I] [DecidableEq I]: M I:= bill 0 1 1 0
def flip (A:M I):= slip I*cc A * slip I
lemma flip_s(I:Type*) [Fintype I] [DecidableEq I]: (slip I)*(slip I)=1:=by simp [slip,bill, Matrix.fromBlocks_multiply]
lemma flip_bills (A B C D: Op I): flip (bill A B C D)=bill (cc D) (cc C) (cc B) (cc A):=by rw [flip,bill_cc]; simp [slip,bill, Matrix.fromBlocks_multiply]
@[simp] lemma flip_star : star (slip I)=slip I:=by unfold slip; rw [bill_star]; simp
lemma slip_unit : slip I∈unitary _:= by constructor<;>rw [flip_star]<;> apply flip_s
lemma flip_sub : flip (U-V)=flip U-flip V:=by unfold flip; rw [cc_sub,mul_sub,sub_mul]
lemma flip_one : flip (1:M I)=1:=by rw [flip,cc_one,mul_one]; apply flip_s
lemma flip_prod : flip (U*V)=flip U*flip V:=by unfold flip; rw [cc_mul]; simp_rw [mul_assoc]; rw [←mul_assoc (slip I) (slip I),flip_s,one_mul]
lemma flip_norm(U:M I): ‖flip U‖= ‖U‖ := by rw [flip, CStarRing.norm_mul_coe_unitary _ (U:=⟨slip I,slip_unit⟩),CStarRing.norm_coe_unitary_mul (U:=⟨slip I,slip_unit⟩)]; exact Scroll.norm_cc U -- tune

def penR (A:Op I):M I := bill A 0 0 (1-cc A)
def camp (P Q:Op I):= (1/2:ℂ) • space P Q
def penL (P Q C: Op I):M I:= bill (Q+camp P Q) (camp P Q *star (cc C)) (cc C*camp P Q) (P+camp P Q)
lemma projRight (p:IsStarProjection A): IsStarProjection (penR A):=by
 refine ⟨?_,?_⟩; · unfold penR bill IsIdempotentElem; rw [Matrix.fromBlocks_multiply,p.isIdempotentElem,show (1-cc A)*(1-cc A)=1-cc A from (ccProj p).one_sub.isIdempotentElem]; simp
 unfold IsSelfAdjoint penR; rw [bill_star,p.isSelfAdjoint, (ccProj p).one_sub.isSelfAdjoint]; simp
lemma reflectedRight(A:Op I): flip (penR A)=1-penR A:=by unfold penR; rw [flip_bills,← show bill (1:Op I) 0 0 (1:Op I)=1 from Matrix.fromBlocks_one,bill_sub]; simp
namespace Deck
variable (p: Deck A P Q C c r)
include p
lemma barUnit : cc C ∈ unitary _ := (ccU ⟨_,p.safety.unit⟩).property
lemma paneP : cc C*P=P*cc C:=by simpa only [cc_mul,p.markA] using congrArg cc p.colorA.eq
lemma paneQ: cc C*Q=Q*cc C:=by simpa only [cc_mul,p.markB] using congrArg cc p.colorB.eq
lemma paneL: cc C * space P Q=space P Q * cc C:=by unfold space; rw [mul_sub,sub_mul,mul_add,add_mul,mul_one,one_mul,p.paneP,p.paneQ]
lemma paneS : star (cc C)* space P Q=space P Q * star (cc C):=by have he:=congrArg star p.paneL; rw [star_mul,star_mul,p.cbP.wall.isSelfAdjoint] at he; exact he.symm
lemma paneZ : Commute (camp P Q) (cc C):=(show Commute (space P Q) (cc C) from p.paneL.symm).smul_left _
lemma wallD : cc (camp P Q)=camp P Q:=by unfold camp space; simp only [cc_smul,cc_sub,cc_one,cc_add,p.markA,p.markB,star_div₀]; norm_num
lemma wall_c : star (camp P Q)=camp P Q:=by rw [camp,star_smul,p.cbP.wall.isSelfAdjoint]; norm_num
lemma reflectedLeft : flip (penL P Q C)=1-penL P Q C:= by
 unfold penL; rw [flip_bills,← show bill (1:Op I) 0 0 (1:Op I)=1 from Matrix.fromBlocks_one,bill_sub]; simp only [cc_add,cc_cc,cc_star,cc_mul,p.markA,p.markB,p.wallD,zero_sub]
 have he:star (cc C)= -C:=by rw [←cc_star,p.safety.antiF]; simp
 rw [he,p.safety.antiF, mul_neg, mul_neg,neg_neg,p.paneZ.eq]; have hx:C*camp P Q=camp P Q*C:=by have h:= congrArg cc p.paneZ.eq; simp only [cc_mul,cc_cc,p.wallD] at h; exact h.symm
 rw [← hx]; congr 1 <;> unfold camp space <;> module
end Deck
end YM.CF.BProof.Double

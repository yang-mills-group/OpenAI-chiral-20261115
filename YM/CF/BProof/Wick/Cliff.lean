import YM.CF.Fock.Salary
import YM.CF.Scroll.Loma
import YM.CF.BProof.Align.Pastel
import YM.CF.BProof.Align.Curt

/-! D_C loss, pairing at gap. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Wick
open Function Filter NormedSpace Fock Finset Branch Align
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][DecidableEq I] [Nonempty I] {A P C: Op I} {c:ℝ}
structure Shelf (A C:Op I)(c:ℝ): Prop where
 proj:IsStarProjection A
 unit:C ∈ unitary _
 sym:Cᵀ= -C
 fee: ‖(1-A)*C*cc A‖ ≤ c
 lid : c<1
lemma plunge {P C: Op I} (p:IsStarProjection P)(g:C ∈ unitary _)(v:Cᵀ= -C)(k:‖P*C-C*cc P‖≤ c)(hc:c<1):Shelf P C c:=by
 let E:=P*C-C*cc P; refine ⟨p,g,v,?_,hc⟩
 rw [show (1-P)*C*cc P=(1-P)*(-E) from by unfold E; rw [neg_sub,mul_sub,←mul_assoc (1-P),←mul_assoc (1-P),qrComplement p]; simp]; exact (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (p.one_sub.norm_le _)).trans ((norm_neg ..).trans_le k))
def offCut(P C:Op I):=P*C*(1-cc P)
def widthP (P C:Op I):=offCut P C *star (offCut P C)
lemma width_pos (P C:Op I): 0≤ widthP P C:= mul_star_self_nonneg _
namespace Shelf
variable (s:Shelf P C c)
include s
lemma antiF : star C = -cc C:= by rw [show star C=(cc C)ᵀ from ccT C]; ext i j; rw [Matrix.transpose_apply]; change star (C j i)= -star (C i j); rw [show C j i= -C i j from Matrix.ext_iff.mpr s.sym i j,star_neg]
lemma fare : ‖offCut P C‖≤ c:=by
 rw [← norm_star (offCut P C)]; unfold offCut; rw [star_mul,star_mul,s.proj.isSelfAdjoint,(ccProj s.proj).one_sub.isSelfAdjoint,s.antiF,neg_mul,mul_neg, norm_neg]; rw [← Scroll.norm_cc]; simp only [cc_sub,cc_one,cc_mul,cc_cc]; rw [← mul_assoc]; exact s.fee
lemma widthN : ‖widthP P C‖≤ c^2:= by rw [widthP,CStarRing.norm_self_mul_star,← pow_two]; exact pow_le_pow_left₀ (norm_nonneg _) s.fare _
lemma pos : 0≤c:= (norm_nonneg _).trans s.fee
lemma small : c^2<1:= pow_lt_one₀ s.pos s.lid (by decide) -- tune
-- Algebra shrink independent of choice LinearOrder & actual Fock.
lemma middle : body P C * star (body P C)+ (1-P)=1-widthP P C:=by
 let V:=cc P; let X:= P*C; have hp:X*star X=P:=by unfold X; rw [star_mul,s.proj.isSelfAdjoint,←mul_assoc,mul_assoc P C, s.unit.2,mul_one,s.proj.isIdempotentElem]
 have ht(q:Op I)(h:IsStarProjection q): X*q*star (X*q)=X*q*star X:=by rw [star_mul,h.isSelfAdjoint,←mul_assoc,mul_assoc X q q,h.isIdempotentElem]
 change X*V*star (X*V)+(1-P)=1-X*(1-V)*star (X*(1-V)); rw [ht V (ccProj s.proj),ht (1-V) (ccProj s.proj).one_sub,mul_sub X,mul_one,sub_mul,hp]; abel
end Shelf
lemma Shoot (t:IsStarProjection A)(e:Align.Twig C A)(g:P*A=0)(h:IsStarProjection P): offCut (A+P) C=offCut P C:=by
 have hz:A*P=0:= swapOrth h t g
 have ht:C*cc A=A*C:=e.symm
 unfold offCut; rw [cc_add,← sub_sub,add_mul,add_mul,mul_sub (A*C),shield e t, show A*C*cc P=0 from (by rw [show A*C=C*cc A from e,mul_assoc,←cc_mul,hz,cc_zero,mul_zero]), sub_zero,zero_add,sub_right_comm (1:Op I),mul_sub, mul_assoc P C (cc A),ht,←mul_assoc P A,g,zero_mul,sub_zero]
end YM.CF.BProof.Wick

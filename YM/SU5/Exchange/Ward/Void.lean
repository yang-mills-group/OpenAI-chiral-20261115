import YM.CF.Sault.Gilt
import YM.CF.Hest.Boat
import YM.CF.Scree.Locus
set_option autoImplicit false
noncomputable section
namespace YM.CF.Sault
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Pastry
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Scree
variable {n m:Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m]
open Thera
open Kennel Hest

-- Section XXI (125): untruncated operator comparison with actual chiral projector.
-- Doesn't assert locality before the J,t tails and masks. Phase including Aim held.
-- Includes the action on FULL excitation space, not just scalar tests. Resulting
-- first-order differential operator on exterior is before conjugating by Reg.
abbrev blockD (P W : Op n): Op n:= P*W*P+(1-P)*W*(1-P)
def inward (P W T:Op n) : Op n := W-(1+capT P T)*blockD P W*(1-capT P T)
abbrev kerLocal (P A W T:Op n): FC n:= Matrix.trace ((P-A)*W) • 1 + dg (inward P W T) -(dg W-Matrix.trace (A*W) • 1)
-- formal derivative (omit identity shift before crane)
abbrev derail(P W:Op n): FC (LeanV n) := let F:=blockD P W; urn (wire true) (trailM true) (F*(1-P))-urn (wire false) (trailM false) (P*F)ᵀ
lemma blockFlow {P: Op n}(W: Op n)(h:IsStarProjection P): P*blockD P W= P*W*P∧ (blockD P W)*P=P*W*P := by
 have G:P*P=P:= h.isIdempotentElem; have hp:(1-P)*P=0:=by rw [sub_mul,G,one_mul,sub_self]
 have hb:P*(1-P)=0:=by rw [mul_sub,G,mul_one,sub_self]
 unfold blockD; constructor
 · rw [mul_add,←mul_assoc,←mul_assoc,G,←mul_assoc,←mul_assoc,hb,zero_mul,zero_mul,add_zero]
 rw [add_mul,mul_assoc (P * W), G, mul_assoc ((1-P)*W),hp,mul_zero,add_zero]
lemma kernelTrace (P W:Op n) (h:IsStarProjection P) : Matrix.trace (P*blockD P W) = Matrix.trace (P*W):=by
 rw [(blockFlow W h).1,Matrix.trace_mul_comm (_*_) P,←mul_assoc,h.isIdempotentElem.eq]

lemma voidPlume (P A W K:Op n)(h:IsStarProjection P)(x:Wave n)(g:Sea P x)(y:Wave (LeanV n)): let c:=acts (exp (dg (capT P K))) x; let L:=ballL (nursery P h) c
 acts (kerLocal P A W K) (L y)= L (acts (-derail P W) y) := by
 intro c L; let F:=blockD P W; let E:=capT P K; let C:=1+E; let D:=1-E; let R:=C*F*D; have v:TagG P E:= tag_g K h
 have u: D*C=1:=v.mud; have u':C*D=1:=mul_eq_one_comm.mp u; have hp:kerLocal P A W K= -(dg R-Matrix.trace (P*F) • 1):=by
    have hd:dg (W-R)=dg W-dg R:=by rw [sub_eq_add_neg,dg_add,dg_neg]; rfl
    unfold kerLocal inward; change Matrix.trace ((P-A)*W) • _ + dg (W-R)-_= _; rw [hd,sub_mul,Matrix.trace_sub,sub_smul,kernelTrace P W h]; abel
 have hu(z:Op n):dg z*quant C=quant C*dg (D*z*C):=zeal D C u z
 have hb: D*R*C=F:=by unfold R; rw [←mul_assoc D (C*F),←mul_assoc D C,u,one_mul,mul_assoc,u,mul_one] -- tune specific
 let B:= ballL (nursery P h) x; have hx(y): L y= acts (quant C) (B y):=by rw [← tallied E v.nil]; exact (lumen h E v x y).symm -- tune tallied
 have tx:= blockFlow W h
 have he:capT P F=0:=by
    unfold capT; rw [mul_assoc,tx.2,←mul_assoc,←mul_assoc,sub_mul,one_mul,h.isIdempotentElem.eq,sub_self,zero_mul,zero_mul]
 have hz0:dg (0:Op n)=0:=by unfold dg dyad; simp
 have hz(z:Wave (LeanV n)): B (acts (faceD true false F) z)=0:=by
    let J:=nursery P h; let Q:=faceD true false F; change B (acts Q z)=_
    rw [← basis_expand z,map_sum,map_sum]; refine Finset.sum_eq_zero (fun i u=>?_)
    rw [map_smul,map_smul,← poked i,←act_mul]; unfold B; rw [Sault.loaf, Scree.fireT]
    · rw [show (nursery P h).eval Q=0 from ?_,zero_mul,act_zero,smul_zero]; exact (birth F P h).trans (he ▸ hz0)
    · exact (face_flour true false F).allP
    exact spanPt _
 have huP: urn (trailM false) (trailM true) (P*F*(1-P))=0:=by
    have hx:P*F*(1-P)=0:=by change P*blockD P W * _= _; rw [tx.1,mul_assoc (P*W),mul_sub,h.isIdempotentElem.eq,mul_one,sub_self,mul_zero]
    rw [hx]; unfold urn; simp
 -- compare conjugate engine & compressed relative action.
 let Y':=(blockFlow W h); have hL:= loft h F x g y
 have hy: B (acts (derail P W+ Matrix.trace (P*F) • 1) y)=acts (dg F) (B y):=by
    have hh: forge (P*F) F (F*(1-P)) (P*F) (P*F*(1-P))= faceD true false F+ (derail P W + Matrix.trace (P*F) • 1):=by rw [forge,huP,add_zero]; unfold derail; dsimp only; unfold F; abel
    change (B (acts _ y))= _ at hL
    rw [hh,act_add,map_add,hz,zero_add] at hL; exact hL
 rw [act_add,act_smul,act_one,map_add,map_smul] at hy
 let U:=quant C; have hq: acts (dg R) (L y)= L (acts (derail P W) y)+Matrix.trace (P*F) • L y:=by
    rw [hx,←act_mul,(hu R),hb,act_mul,←hy,map_add,map_smul,←hx,←hx]
 have hσ(Z:FC n)(x:Wave n): acts (-Z) x= -acts Z x:=by rw [←neg_one_smul ℂ,act_smul,neg_one_smul]
 rw [hp,hσ,act_sub,act_smul,act_one,hq]; rw [←neg_one_smul ℂ (derail P W),act_smul,map_smul,neg_one_smul]; abel

end YM.CF.Sault

import YM.CF.Sault.Gilt
import YM.CF.Sault.Govern

/-!
 # The sub-top, actual-AIM charges of XXI

 Eq.(125) at finite regulator. `C` in code is the Leg only, C*C=0.
 Keep also its operator on the full symbol spaces Dwell, on the `ballL` for `relV`
 (insert Marks on THIS map when doing all-layout Keys). Not substituting for Force.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.StressExchange
open Function Filter Metric Lattice Finset Fock Lat Spire Scroll Drapes Rush Pastry Thera Sault Proa Hest Scree Kennel NormedSpace
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {I : Type*} [LinearOrder I] [Fintype I]
variable (S A C W : Op I)
def preserve : Op I := S*W*S + (1-S)*W*(1-S)
def legTax : ℂ := Matrix.trace ((S-A)*W)
def inhibit : Op I := W - (1+C)*preserve S W*(1-C)
def Zcharge : FC I := legTax S A W • 1 + dg (inhibit S C W) -
    (dg W - Matrix.trace (A*W) • 1)
variable {S A C}
lemma preserve_block (p:IsStarProjection S) : Commute S (preserve S W):= by
 have ht:=p.isIdempotentElem.eq; have hv:S*(1-S)=0:=by rw [mul_sub,mul_one,ht,sub_self]
 have hu:(1-S)*S=0:=by rw [sub_mul,one_mul,ht,sub_self]
 change S*_=_*S; unfold preserve; rw [mul_add,add_mul]
 rw [←mul_assoc S _ (1-S),←mul_assoc S (1-S) W,hv,zero_mul,zero_mul]; simp only [mul_assoc ( (1-S)*W),hu,mul_zero]
 rw [←mul_assoc S _ S,←mul_assoc S,ht,mul_assoc _ S S,ht] -- tune
lemma trace_preserve (p:IsStarProjection S): Matrix.trace (preserve S W)=W.trace:=by
 have hx (U:Op I)(p:IsStarProjection U):Matrix.trace (U*W*U)= Matrix.trace (U*W):=by rw [Matrix.trace_mul_comm,←mul_assoc,p.isIdempotentElem.eq]
 rw [preserve,Matrix.trace_add,hx S p,hx _ p.one_sub,sub_mul,one_mul,Matrix.trace_sub]; abel
lemma inhibit_nullTrace (p:IsStarProjection S)(h:TagG S C): (inhibit S C W).trace=0:= by
 rw [inhibit,Matrix.trace_sub,Matrix.trace_mul_comm,←mul_assoc, h.mud,one_mul,trace_preserve W p,sub_self]
lemma frozen_trace (p:IsStarProjection S): (S*preserve S W).trace=(S*W).trace:= by
 have hv:S*(1-S)=0:=by rw [mul_sub,mul_one,p.isIdempotentElem.eq,sub_self]
 rw [preserve,mul_add,←mul_assoc S _ (1-S),←mul_assoc S (1-S),hv,zero_mul,zero_mul, add_zero, ←mul_assoc S _ S,←mul_assoc, p.isIdempotentElem.eq,Matrix.trace_mul_comm,←mul_assoc, p.isIdempotentElem.eq]
lemma dgMinus (U V:Op I) : dg (U-V)=dg U-dg V:=dyad_sub ..
/-- conjugation all layout. -/
lemma Zrecord (A:Op I)(h:TagG S C) :
 Zcharge S A C W*exp (dg C)=exp (dg C)*(Matrix.trace (S*W) • 1-dg (preserve S W)):= by
 have ht:Zcharge S A C W=Matrix.trace (S*W) • 1 - dg ((1+C)*preserve S W*(1-C)):=by unfold Zcharge inhibit legTax; rw [sub_mul,Matrix.trace_sub,sub_smul,dgMinus]; abel
 have hx:Commute (((S*W).trace) • (1:FC I)) (exp (dg C)):= (Commute.one_left _).smul_left _
 rw [ht, sub_mul,mul_sub (exp (dg C)),hx.eq, tallied _ h.nil, Sault.zeal (1-C) (1+C) h.mud]; congr 1
 apply congrArg _ ?_ ; apply congrArg (dg (n:=I))
 rw [←mul_assoc,←mul_assoc,h.mud,one_mul,mul_assoc,h.mud,mul_one]
lemma Zvoid (A:Op I)(h:TagG S C)(p:IsStarProjection S)(x:Wave I)(hx:Sea S x):
   acts (Zcharge S A C W) (acts (exp (dg C)) x)=0:=by rw [←act_mul,Zrecord W A h,act_mul,act_sub,act_smul,act_one,Sault.loft_v _ (preserve_block W p) p x hx,frozen_trace W p,sub_self,map_zero]

def creditD (B:Op I) : FC (LeanV I) := urn (wire true) (trailM true) (B*(1-S)) - urn (wire false) (trailM false) (S*B)ᵀ -- `S` implicit? declared implicit via variable {S}, notation

def coinZ (S W:Op I) : FC (LeanV I) := -creditD (S:=S) (preserve S W)
lemma voidCoin (S:Op I): acts (coinZ S W) (vacuum (LeanV I))=0:=by unfold coinZ creditD; rw [act_neg,act_sub,Sault.urn_stop,Sault.urn_stop,sub_self,neg_zero]

-- Unlike using Sault.plume without modifying the operator, remove faceD part:
-- its eval is zero as an exterior polynomial AFTER polarization, but here want exactly
-- no pure emission. Can use even for noncommuting-with-A sources.
lemma deadFace (B:Op I)(p:IsStarProjection S)(h:Commute S B) (x:Wave I)(y:Wave (LeanV I)):
 ballL (nursery S p) x (acts (faceD true false B) y)=0:=by
 -- prove ballL multiplication for FLour sector on all y then Hest.birth
 let v:=nursery S p; let g:=boat B; have he:g.val=faceD true false B:=rfl
 have hw:capT S B=0:=by unfold capT; rw [mul_assoc, ←h.eq, ←mul_assoc,sub_mul,one_mul,p.isIdempotentElem.eq,sub_self,zero_mul]
 have hv:v.eval g.val=0:=by change v.cook _=_; rw [birth,hw]; simp [dg,dyad] -- tune
 -- math proof use wire individually plus zz. search
 rw [←basis_expand y,map_sum,map_sum]
 apply Finset.sum_eq_zero; intro i _; rw [map_smul,map_smul,← Pastry.poked i, ←act_mul,loaf]; -- tune
 rw [fireT (nursery S p) (face_flour true false B).allP (spanPt i), ← he, hv, zero_mul, act_zero, smul_zero]

lemma truncZ (A:Op I)(h:TagG S C)(p:IsStarProjection S)(x:Wave I)(hx:Sea S x)(y:Wave (LeanV I)):
 let L:= ballL (nursery S p) (acts (exp (dg C)) x); L (acts (coinZ S W) y)=acts (Zcharge S A C W) (L y):=by
 intro L; let B:=preserve S W; let P:=ballL (nursery S p) x; have hu:=Sault.loft p B x hx y; let Y:= creditD (S:=S) B
 have hp:= preserve_block W p; have ht:S*B*(1-S)=0:=by rw [show S*B=B*S from hp.eq,mul_assoc,mul_sub S, p.isIdempotentElem.eq,mul_one,sub_self,mul_zero]
 have hg:forge (S*B) B (B*(1-S)) (S*B) (S*B*(1-S))=Y + (S*W).trace • 1+faceD true false B:= by unfold Y creditD forge; rw [ht, show (S*B).trace=_ from (show (S*B).trace= _ from frozen_trace W p),show urn (trailM (n:=I) false) (trailM true) 0=0 from by simp [urn]]; abel
 dsimp only at hu; rw [hg,act_add,act_add,act_smul,act_one,map_add,map_add,map_smul,deadFace B p hp] at hu
 change P (acts Y y)+(S*W).trace • P y + 0=acts (dg B) (P y) at hu
 have hp(t): L t= acts (exp (dg C)) (P t):=(Sault.lumen p C h x _).symm
 rw [hp,hp,←act_mul (Zcharge S A C W), Zrecord W A h,act_mul,act_sub,act_smul,act_one,← (show _=acts (dg (preserve S W)) (P y) from hu)]; change acts _ (P (acts (-Y) y))=_; rw [act_neg,map_neg]; congr 1; abel
end YM.CF.StressExchange

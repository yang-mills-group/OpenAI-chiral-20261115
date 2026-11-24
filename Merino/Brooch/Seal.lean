import YM.SU5.Exchange.Ward.Void

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 520000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Brooch
open Function Finset Fock Scroll Spire Sault
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Thera Kennel Hest

abbrev hing {X:Type*}[Neg X](r:Bool)(x:X):X:=if r then -x else x
variable {n:Type*}[Fintype n][LinearOrder n](b r:Bool)(V:UNI n)

def form (W:Op n):Op n:= if r then star (sings b V W) else sings b V W
def notch (P W T:Op n):Op n:= (1+capT P T)*blockD P W*(1-capT P T)



lemma sew_add(A B:FC n): tourP V b r (A+B)=tourP V b r A+tourP V b r B:=by cases r <;> unfold tourP <;> simp only [Bool.false_eq_true,↓reduceIte,singT,win_a,map_add,theta_add]
lemma sew_sub(A B:FC n): tourP V b r (A-B)=tourP V b r A-tourP V b r B:=by
 cases r <;> unfold tourP <;> simp only [Bool.false_eq_true,↓reduceIte,singT,win_l,map_sub,theta_sub]
lemma sew_scale(c:ℂ)(A:FC n):tourP V b r (c • A)= cSignX (b.xor r) c • tourP V b r A:=by
 cases b <;> cases r <;>
   simp [tourP, windX,twist_scalar,cSignX,cc_smul,theta_smul]
lemma coin_one:tourP V b r (1:FC n)=1 := by
 cases r <;> cases b <;> simp [tourP,windX,theta_one]
lemma stamp(C:Op n):Matrix.trace (twist V C)= C.trace:=by
 rw [twist_formula,Matrix.trace_mul_comm (V.val*C) _, ←mul_assoc,V.property.1,one_mul]
lemma tint(C:Op n):Matrix.trace (windX b C)=cSignX b C.trace:=by cases b; rfl; change Matrix.trace (cc C)=star (Matrix.trace C); simp only [Matrix.trace, Matrix.diag_apply, star_sum, cc_apply]


lemma coin(C:Op n):
  tourP V b r (C.trace • 1)=(form b r V C).trace • 1:=by
 rw [sew_scale,coin_one]
 cases r; rw [Bool.xor_false]; unfold form; simp only [Bool.false_eq_true,↓reduceIte,singT,stamp,tint]
 change _=(star (twist V (windX b C))).trace • 1
 have hstar(D:Op n): Matrix.trace (star D)=star D.trace:=Matrix.trace_conjTranspose _
 rw [hstar,stamp,tint]
 cases b; rfl
 change _=star (star _ ) • _
 rw [star_star]; rfl
lemma dd(C:Op n):
  tourP V b r (dg C)= if r then (form b r V C).trace • 1-dg (form b r V C) else dg (form b r V C):=by
 have hd:windX b (dg C)=dg (windX b C):=by cases b; rfl; exact dg_clear _
 cases r
 · change twist (quantU V) (windX b _)=dg (twist V _)
   rw [hd,dg_cov]
 change theta V (windX b _)=(star (twist V _)).trace • 1- dg (star (twist V (windX b C)))
 have hstar(D:Op n): Matrix.trace (star D)=star D.trace:=Matrix.trace_conjTranspose _
 rw [hd, theta_dg, map_star, hstar,stamp]


variable {P P' T:Op n} (f:sings b V P=swapX r P') (h':IsStarProjection P')
include f h' in
lemma clip(W:Op n):
 form b r V (notch P W T) = notch P' (form b r V W) (jazz r (sings b V T)):=by
 cases r
 · change twist V (windX b P) = P' at f
   change twist V (windX b _) = notch P' (twist V _) (twist V _)
   simp only [notch,capT,blockD,win_m,win_l,win_i,win_a,map_mul,map_sub,map_one,map_add,f]
 change twist V (windX b P)=1-P' at f
 change star (twist V (windX b _))= notch P' (star (twist V _)) (-star (twist V _))
 have h1:1-(1-P')=P':=by abel
 have h2:star P'=P':=h'.isSelfAdjoint
 simp only [notch,capT,blockD,win_m,win_l,win_i,win_a,map_mul,map_sub,map_one,map_add,
     star_mul,star_sub,star_one,f,h1,h2,star_add,mul_neg,neg_mul,sub_neg_eq_add,mul_assoc]
 rw [←sub_eq_add_neg,add_comm (a:=(1-P') * _ )]; -- tune


lemma notchTr(P W T:Op n)(h:IsStarProjection P):
  (notch P W T).trace=W.trace:=by
 let Y:=1-P
 have hp:P*P=P:=h.isIdempotentElem
 have hb:Y*Y=Y:=by unfold Y; rw [mul_sub,mul_one,sub_mul,one_mul,hp,sub_self,sub_zero]
 let Q:=capT P T
 change ((1+Q)*(P*W*P+Y*W*Y)*(1-Q)).trace=_
 rw [Matrix.trace_mul_comm _ (1-Q),←mul_assoc,show (1-Q)*(1+Q)=1 from (tag_g T h).mud,one_mul,
     Matrix.trace_add,Matrix.trace_mul_comm (P*W) _,←mul_assoc,hp,Matrix.trace_mul_comm (Y*W) _,←mul_assoc,hb,
     ←Matrix.trace_add,←add_mul, show P+Y=1 by unfold Y; abel,one_mul]
lemma basic(P A W T:Op n):
 kerLocal P A W T=(P*W).trace • 1 - dg (notch P W T):=by
 have hd:dg (W-notch P W T)=dg W-dg (notch P W T):=by rw [sub_eq_add_neg,dg_add,dg_neg]; rfl
 unfold kerLocal inward
 unfold notch at hd ⊢
 rw [sub_mul,Matrix.trace_sub,sub_smul,hd]; abel

include f h'
lemma compass(Ptarget : Op n) -- target tick (independent)
   (A W:Op n):
 tourP V b r (kerLocal P A W T)= hing r (kerLocal P' Ptarget (form b r V W) (jazz r (sings b V T))):=by
 rw [basic,basic,sew_sub,coin,dd,clip b r V f h']

 cases r
 · have e: form b false V (P*W)= P'*form b false V W:=by
       change twist V (windX b P)=P' at f
       change twist V (windX b _) = _
       rw [win_m,map_mul,f]; rfl
   rw [e]; rfl
 let Y:=form b true V W; let T':=jazz true (sings b V T); let K:=notch P' Y T'
 have h1: form b true V (P*W)= Y*(1-P'):=by
    change twist V (windX b P)=1-P' at f
    change star (twist V (windX b _)) =_
    rw [win_m,map_mul,f,star_mul,star_sub,star_one,show star P'=P' from h'.isSelfAdjoint]; rfl
 rw [if_pos rfl, h1,notchTr _ _ _ h',Matrix.trace_mul_comm Y _,sub_mul,one_mul,Matrix.trace_sub,sub_smul]
 change ((Y.trace • _ - (P'*Y).trace • _) - (_ • _ - dg K)) = -((P'*Y).trace • _ -dg K)
 abel
end YM.CF.Merino.Brooch

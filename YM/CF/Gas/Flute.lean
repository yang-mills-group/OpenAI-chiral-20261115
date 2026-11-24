import YM.CF.Gas.Grade
import YM.CF.Scree.Form
set_option autoImplicit false
noncomputable section
namespace YM.CF.Gas
open Function Filter Metric Finset NormedSpace Fock Petal Pastry Spire Scroll Scree
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Type*}[Fintype n][LinearOrder n]
variable {P H C Y:Op n}(h:IsStarProjection P)(e:IsUnit (stage P C))
local notation "V"=>reserve P C
local notation "W"=> weldB P C
local notation "Q"=> ((1:Op n)-P)
local notation "B"=> cc Q
include h e
lemma mir_V (k:C ∈ unitary _) (p:Cᵀ= -C) : reserve Q C= -(cc W):=by
 let S:= C-C*V*C; have hS: S*cc P=0:=by
    have hp: V*C*cc P=cc P:=by
       have ht:=reserve_il h e; rw [body,←mul_assoc,←mul_assoc,reserve_r h] at ht; exact ht
    unfold S; rw [sub_mul, mul_assoc,mul_assoc C V,←mul_assoc V]; -- tune
    rw [hp,sub_self]
 have hy: S*B=S:=by rw [cc_sub,cc_one,mul_sub,hS,mul_one,sub_zero]
 have hz:C*star C=1:= (show C∈unitary _ from k).2 -- iff
 have ht: (1-P)*P=0:=by rw [sub_mul,one_mul,h.isIdempotentElem,sub_self]
 have he: (1-P)*C*V*(1-P)=0:=by rw [mul_assoc ((1-P)*C),mul_sub,mul_one,reserve_r h,sub_self,mul_zero]
 have hx: W*(star (body Q C))= 1-P:=by
    change ((1-P)*S*cc (1-P))*star ((1-P)*C*cc (1-P))=_; rw [mul_assoc (1-P), hy, star_mul,star_mul, show star B=B from (ccProj h.one_sub).isSelfAdjoint, show star (1-P)=1-P from h.one_sub.isSelfAdjoint]
    -- remove B against right support
    change (1-P)*S*(B*(star C*(1-P)))= _; rw [←mul_assoc _ B, mul_assoc (1-P) S B,hy]; unfold S; rw [mul_sub,sub_mul, ←mul_assoc ((1-P)*C),mul_assoc (1-P) C, hz,mul_one,h.one_sub.isIdempotentElem,←mul_assoc,←mul_assoc (1-P), ←mul_assoc (1-P)] -- tune
    rw [mul_assoc ((1-P)*C*V), hz,mul_one,he, sub_zero]

 have ho: W= body Q S:=rfl
 have hb: W*B=W:=by rw [ho,body_right h.one_sub] -- inconsistency rhs Q goal tune
 have hf: (-(cc W))*(body Q C)=B:=by
    have hu:=congrArg cc hx; rw [cc_mul,show cc (star (body Q C))= -(body Q C) from (by rw [cc,star_star,body_skew h.one_sub p]),mul_neg] at hu; rw [neg_mul]; exact hu
 have hE : IsUnit (stage Q C) := by rw [stage,show 1-Q=P by abel,add_comm]; exact e
 let R:=reserve Q C
 change R= _
 calc
    R = B*R := (reserve_l h.one_sub hE).symm
    _ = (-cc W) * Q:=by rw [←hf,mul_assoc,show _ * R=1-P from reserve_ir h.one_sub hE]
    _ = _:=by have ht:=congrArg cc hb; simp only [cc_mul, cc_cc] at ht; rw [neg_mul,ht]  -- wrong. calc
lemma mir_A (p:C ∈ unitary _) : driftB Q C = -(star (driftB P C)):=by
 let D:=reserve Q C
 have hk:C*star C=1:=p.2; have hg:=ccProj h.one_sub
 have h0:P*star V=star V := by nth_rw 1 [← show star P=P from h.isSelfAdjoint]; rw [←star_mul,reserve_r h]
 have ht : V*(P*C*cc P)=cc P:= reserve_il h e
 have hy:=congrArg star ht; rw [star_mul,star_mul,star_mul,show star P=P from h.isSelfAdjoint, show star (cc P)=cc P from (ccProj h).isSelfAdjoint,mul_assoc, mul_assoc,h0] at hy
 let Z:=star (driftB P C)
 have hB:Z= -(B*star C*star V):=by unfold Z driftB; rw [star_neg,star_mul,star_mul, show star B=B from hg.isSelfAdjoint, mul_assoc]
 have he : B*Z=Z:=by rw [hB,mul_neg,←mul_assoc,←mul_assoc,hg.isIdempotentElem]
 have hz:(1-P)*star V=0:=by rw [sub_mul,one_mul,h0,sub_self]
 have h':  body Q C * Z=(1-P)*C*cc P:=by -- tune
    rw [body,mul_assoc _ B,he,hB,mul_neg,←mul_assoc,←mul_assoc,cc_sub,cc_one]
    rw [mul_sub (_*C),mul_one,sub_mul,sub_mul]; nth_rw 1 [mul_assoc (1-P) C]; rw [hk,mul_one,hz,zero_sub,neg_neg]; rw [mul_assoc _ _ (star C), mul_assoc,mul_assoc,mul_assoc (cc P), hy,mul_assoc]; -- tune
 have hE : IsUnit (stage Q C) := by rw [stage,show 1-Q=P by abel,add_comm]; exact e
 change driftB _ _= -Z; rw [driftB,show 1-Q=P by abel]; congr 1
 calc
    _ = reserve Q C*((1-P)*C*cc P) := by rw [←mul_assoc,←mul_assoc,reserve_r h.one_sub]
    _ = Z :=by rw [← h',←mul_assoc,reserve_il h.one_sub hE,he]
end YM.CF.Gas

import YM.SU5.LitCurrent.Transport
import YM.CF.Hive.Hen
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "I" => Single N
/-!
Reflection centering: use both the literal 127 J, and optionally subtract a
real multiplier times trace J (same for each axis). For divergence of the full
parts this subtracts zero. It allows making Y_s transport with sign under all
odd Sweeps, even AFTER masking. Algebra for transport, on even Fock only.
-/
section math
variable {n:Type}[LinearOrder n][Fintype n](U:UNI n)(b z:Bool)(J:Op n)
local notation "O"=>Urn.lotB b z U
local notation "U1"=>doveL b z U -- ambig
local notation "V"=> ech
abbrev liftHalf (z:ℝ)(J:Op n):FC n:=dg J- (z:ℂ) • (J.trace • 1)
abbrev preHalf (z:ℝ)(A J:Op n):FC n:= preJ A J- (z:ℂ) • (J.trace • 1)
private lemma shift_one (t:ℂ): O (t • 1)= cSignX (b.xor z) t • 1:=by
 rw [Urn.visage,map_one]
private lemma tracing : O (dg J)=(if z then ((U1 J).trace • (1:FC n)) else 0)+Scroll.hush z (dg (U1 J)):= by
 have he: windX b (dg J)= dg (windX b J):=by cases b; rfl; exact dg_clear _
 cases z; swap
 · change theta U (windX b (dg J))=_ ; simp only [ite_true,hush_true]
   rw [he, theta_dg]; have ht:star (windX b J).trace= (doveL b true U J).trace:=by rw [Sault.lune,win_trace]; cases b<;> simp [cSignX]
   change _= _; rw [ht,sub_eq_add_neg,map_star (twist U)]; rfl -- check rw dir
 change sings b (quantU U) (dg J)=_
 simp only [Bool.false_eq_true,ite_false,hush_false,zero_add]; rw [singT,he,dg_cov]; rfl
lemma lotHalf : O (liftHalf (1/2:ℝ) J)=Scroll.hush z (liftHalf (1/2:ℝ) (U1 J)):=by
 unfold liftHalf; rw [map_sub,Urn.visage,shift_one,tracing,Sault.lune]; cases b <;>cases z<;> simp only [Bool.false_xor,Bool.xor_false,Bool.xor_self,ite_true,Bool.false_eq_true,ite_false,hush_true,hush_false,cSignX,Complex.star_def,Complex.conj_ofReal,zero_add] -- attempt collector
 all_goals
    module

lemma carryPre (A W: Op n)(g:sings b U A=swapX z W)(h:IsStarProjection W) : O (preHalf (1/2:ℝ) A J)=Scroll.hush z (preHalf (1/2:ℝ) W (U1 J)):=by
 let p:=h.isSelfAdjoint
 have ht: (A*J*(1-A)).trace=0:=by
    -- S projection via frame. trace U1 kills (either z)
    have hp:sings b U (A*J*(1-A))= swapX z W *sings b U J*(1-swapX z W):=by rw [singm,singm,show sings b U (1-A) = 1-sings b U A from (by simp [win_i]),g]
    have he(i:Op n): (sings b U i).trace=cSignX b i.trace:=by rw [singT,trace_twist,win_trace]
    have hz(X Y:Op n)(p:IsStarProjection X):(X*Y*(1-X)).trace=0:=by rw [Matrix.trace_mul_comm (X*Y),←mul_assoc,sub_mul,one_mul,p.isIdempotentElem.eq,sub_self,zero_mul,Matrix.trace_zero]
    have hx: IsStarProjection (swapX z W):=by cases z; exact h; exact h.one_sub
    have hx':= (he (A*J*(1-A))).symm.trans ((congrArg Matrix.trace hp).trans (hz _ _ hx))
    cases b; exact hx'; exact star_eq_zero.mp hx'
 have hM(X Y:Op n):sings b U (X-Y)=sings b U X-sings b U Y:=by simp
 have hI:sings b U 1=1:=by simp [win_i]
 let B:= A*J*(1-A); have he:sings b U B = swapX z W * sings b U J * (1-swapX z W):=by rw [show B=A*J*(1-A) from rfl, singm,singm,hM,hI,g]
 have hu: U1 B=W*(U1 J)*(1-W):=by
    unfold Sault.doveL; rw [he]; cases z; rfl
    simp only [swapX,ite_true,sub_sub_cancel,star_mul,h.isSelfAdjoint.star_eq,h.one_sub.isSelfAdjoint.star_eq,mul_assoc]
 have hg:cSignX (b.xor z) ((A*J).trace)= if z then (U1 J).trace - (W*U1 J).trace else (W*U1 J).trace:=by
    rw [←Sault.lune b z U]; unfold Sault.doveL; rw [singm,g]; cases z; rfl
    simp only [ite_true,swapX,star_mul,h.one_sub.isSelfAdjoint.star_eq]; rw [Matrix.trace_mul_comm _ (1-W),sub_mul,one_mul,Matrix.trace_sub]
 change O _=_
 unfold preHalf preJ; rw [map_sub,map_add,shift_one,Urn.visage,shift_one,tracing,Sault.lune b z U (A*J*(1-A)),ht]; -- tune final algebra
 -- rw goal inspect
 simp_rw [show A*J*(1-A)=B from rfl,hu,hg,←Sault.lune b z U J] -- tune p lhs see
 cases z<;> cases b <;> simp only [Bool.false_eq_true, Bool.false_xor, Bool.xor_self, Bool.xor_false,ite_false,ite_true,hush_false,hush_true,cSignX,zero_add,add_zero,Complex.star_def,Complex.conj_ofReal,map_zero,zero_smul]
 all_goals module
end math
end YM.CF.LitCurrent

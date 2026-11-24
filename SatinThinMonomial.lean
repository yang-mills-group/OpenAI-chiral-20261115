import SatinThinQuad
import YM.CF.Ione.Tape
/-! Necessary even at *high* degrees. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.QuadClock
open Spire Ione Fock Lat Lattice Wilson Laurent Rush Drapes Fir Peaks Dial Paige Scroll Hive Cube Skye
open Matrix Thera Levier Urn Hake Pastry Scree Stilo
open Function Filter Finset
open scoped Classical Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra

private def gradeQ : SpinIdx→ℂ:=![1,1,-1,-1]
private def spinSide : SpinIdx→ℂ:=![Complex.I,-Complex.I,Complex.I,-Complex.I]
private lemma grade_c : grading=Matrix.diagonal gradeQ:=by ext x y; fin_cases x<;>fin_cases y<;>norm_num [grading,Matrix.diagonal_apply,gradeQ]
private lemma cliff_c : gammaOp 0*gammaOp 1=Matrix.diagonal spinSide:=by
 ext x y; fin_cases x<;>fin_cases y<;> norm_num [gammaOp,spinSide,Matrix.mul_apply,Fin.sum_univ_succ, SpinIdx,Matrix.diagonal_apply]
private lemma spinSideI (x y:SpinIdx)(p:gradeQ x=gradeQ y)(u:spinSide x=spinSide y): x=y:=by
 have t:=congrArg Complex.im u
 fin_cases x<;>fin_cases y<;> first|rfl|norm_num [gradeQ,spinSide] at t <;> norm_num [gradeQ] at p
section
open Scroll
variable {a:Signed}{U:UNI SpinIdx}{b c:Bool}(h:JetS a c b U)
include h
lemma cliffPlane (u:Quad a) : ∃ t:Bool, sings c U (gammaOp 0*gammaOp 1)= Scroll.hush t (gammaOp 0*gammaOp 1):=by
 let C:=gammaOp 0*gammaOp 1; have ht : sings c U (gammaOp (a.perm 0)* gammaOp (a.perm 1)) = Scroll.hush ((a.flip 0).xor (a.flip 1)) C:=by
    rw [singT,win_m,map_mul,←singT,←singT,show sings c U (gammaOp (a.perm 0))=_ from h.cliff 0,show sings c U (gammaOp (a.perm 1))=_ from h.cliff 1]; dsimp only [C]; cases a.flip 0 <;> cases a.flip 1<;> simp
 rcases u.lo with h₀|h₁
 · exact ⟨(a.flip 0).xor (a.flip 1),by rwa [h₀.1,h₀.2] at ht⟩
 rw [h₁.1,h₁.2,gammaSwap (1:Axis) 0 (by decide),singT,win_n,map_neg,←singT] at ht
 refine ⟨!((a.flip 0).xor (a.flip 1)),?_ ⟩
 change sings c U (gammaOp 0*gammaOp 1)=_
 generalize HZ:(a.flip 0).xor (a.flip 1)=c' at *
 cases c'<;> simp only [hush_true,hush_false,C,Bool.not_false,Bool.not_true] at *
 · simpa using congrArg Neg.neg ht
 exact neg_injective ht
omit h in
private lemma plane_chi (i j:SpinIdx)(u: SpinIdx→ℂ)(b:Bool)(p: twist U (diagonal u)= Scroll.hush b (diagonal u))(w:U.val i j≠0): u j= Scroll.hush b (u i):=by
 have hp:= (congrArg (·*U.val) p)
 rw [twist_formula,mul_assoc (U.val*_),(show star U.val *U.val=1 from U.property.1),mul_one] at hp
 have ht:= Matrix.ext_iff.mpr hp -- ext_iff direction?
 apply mul_left_cancel₀ w; rw [mul_comm (U.val i j) (Scroll.hush b (u i))] -- tune id trick
 cases b<;> simpa [Matrix.diagonal_mul, Matrix.mul_diagonal] using ht i j

def monomial {_n:Type*}(W:Op _n): Prop:= ∀ i i' j, W i j≠0→W i' j≠0→ i=i'
lemma spinMon (u:Quad a): monomial U.val:=by
 have p': twist U (diagonal gradeQ)= Scroll.hush b (diagonal gradeQ):=by
    rw [← grade_c]; have hg:=h.grade; cases c; exact hg; rw [singT (p:=true),show windX true grading=grading from ?_] at hg; exact hg
    ext x y; fin_cases x <;> fin_cases y <;> norm_num [grading,windX]
 obtain ⟨t,u⟩:=cliffPlane h u; rw [cliff_c] at u
 obtain ⟨r,hw⟩:∃ r:Bool, twist U (diagonal spinSide)=Scroll.hush r (diagonal spinSide):=by
    -- diagonal reverses on conjugation.
    cases c
    · exact ⟨t,u⟩
    rw [singT (p:=true),show windX true (diagonal spinSide)= -diagonal spinSide from ?_,map_neg] at u
    · refine ⟨!t,?_⟩; cases t; exact neg_eq_iff_eq_neg.mp u; exact neg_injective u
    ext x y; by_cases h:x=y; subst x; fin_cases y <;> norm_num [spinSide,Matrix.diagonal_apply,windX]; simp [windX,h, Matrix.diagonal_apply]
 intro i i' j hz hv
 have hp (v:SpinIdx→ℂ)(q:Bool)(w:twist U (diagonal v)=Scroll.hush q (diagonal v)) : v i=v i':=by
    have h:=(plane_chi i j v q w hz).symm.trans (plane_chi i' j v q w hv); cases q <;> simpa using h
 exact spinSideI i i' (hp gradeQ b p') (hp spinSide r hw)
end
lemma prepMon {n:Side}(s:Shape)(c:Bool){U:UNI SpinIdx}(t:monomial U.val): monomial (prepU s U (xtra c) n).val:=by
 rintro ⟨⟨i,x⟩,b⟩ ⟨⟨j,y⟩,d⟩ ⟨⟨k,z⟩,e⟩ p q
 have hg (i:Site n)(x:SpinIdx)(b:SU.Slot)(t:(prepU s U (xtra c) n).val ((i,x),b) ((k,z),e) ≠0): Tofu s n i=k ∧ U.val x z≠0∧ b=e:=by
    change jump (Tofu s n) (fun i=> (milU s U (xtra c) i).val) (i,x,b) (k,z,e)≠0 at t; rw [jump_apply] at t; by_cases h:Tofu s n i=k; swap; · exact False.elim (t (if_neg h))
    rw [if_pos (show _ from h)] at t
    change s.payA i*(U.val x z*(1:Op SU.Slot) b e)≠ 0 at t
    have hu:=right_ne_zero_of_mul t; exact ⟨h,left_ne_zero_of_mul hu,(by by_contra hg; apply right_ne_zero_of_mul hu; rw [Matrix.one_apply,if_neg hg])⟩
 obtain ⟨A,B,C⟩:=hg _ _ _ p; obtain ⟨D,E,F⟩:=hg _ _ _ q; exact Prod.ext (Prod.ext ((Tofu s n).injective (A.trans D.symm)) (t _ _ _ B E)) (C.trans F.symm)

lemma praiseMon {n:Side}(s:Sweep n)(g:s∈cycleSweep n): monomial (praise s).val:=by
 unfold praise; let r:= detX s.s; let U:=siteU (castX s) s.charge (spinU s.charge s.s) n
 rintro ⟨i,x⟩ ⟨j,y⟩ ⟨k,z⟩ p q; have h (a:Bool)(t)(u:(spice U r).val (a,t) (k,z)≠0): a=k.xor r ∧ U.val t z≠0:= ⟨by rw [Urn.cream] at u; by_contra g; exact u (if_neg g), mt (spice_E U r (a,t) (k,z)) u⟩ -- tune LeanV
 obtain ⟨e,t⟩:=h i x p; obtain ⟨w,v⟩:=h j y q; exact Prod.ext (e.trans w.symm) (prepMon (castX s) s.charge (spinMon (spinZ _ s.s) ((cycleQ _).mp g)) x y z t v)

section quant
variable {n:Type*}[LinearOrder n][Fintype n]{W: Op n}(t:monomial W)
include t
lemma wedgeMon (s:Finset n):∃ (a:Finset n)(b:ℂ), wedge W s=b • basisKet a:=by
 induction s using induction_on_min with
 | empty => exact ⟨∅,1,(wedge_empty _).trans (one_smul ..).symm⟩
 | insert i s g ih =>
   obtain ⟨a,b,p⟩:= ih; rw [wedge_min _ _ _ g,p]; by_cases h: ∃ j,W j i≠0; swap
   · push Not at h
     rw [show acts W (basisKet i)=0 from PiLp.ext fun j=> (basis_act ..).trans (h j)]
     exact ⟨∅,0,by simp⟩
   obtain ⟨j,u⟩:=h; rw [show acts W (basisKet i)= W j i • (basisKet j) from ?_,map_smul (create ..)] -- tune
   · rw [create_put,act_smul,map_smul, put_act]; split
     next => exact ⟨∅,0,by simp⟩
     next => rw [smul_smul,smul_smul]; exact ⟨_,_,rfl⟩
   apply PiLp.ext; intro k; rw [basis_act]; change _= W j i*(basisKet _).ofLp _; rw [basis_apply]; split; next w => rw [mul_one]; exact congrArg (fun k=> W k i) w -- tune direction
   next p => rw [mul_zero]; by_contra he; exact p (t k j i he u)
lemma quantMon : monomial (quant W):=by
 intro i i' j p q; obtain ⟨a,b,w⟩:= wedgeMon t j
 have ht(i:Finset n)(p:quant W i j≠0): i=a:=by unfold quant at p; rw [Matrix.of_apply,w] at p; change b*(basisKet a).ofLp i≠0 at p; by_contra x; rw [basis_apply,if_neg x,mul_zero] at p; exact p rfl
 exact (ht i p).trans (ht i' q).symm
end quant
lemma penny {n:Side}(s:Sweep n)(h:s∈cycleSweep n)(z:Finset (Dwell n)): (∑ i:Finset (Dwell n),‖(hail_Q s).val i z‖)≤1:=by
 let U:=hail_Q s; have ht:monomial U.val:=quantMon (praiseMon s h); by_cases g:∃ j,U.val j z≠0
 · obtain ⟨j,p⟩:=g; rw [sum_eq_single j]
   · exact (norm_entry ..).trans (CStarRing.norm_of_mem_unitary (hail_Q s).property).le
   intro i _ x; rw [norm_eq_zero]; exact Classical.byContradiction (fun w=>x (ht _ _ z w p))
   simp
 push Not at g
 simp_rw [show ∀ j,(hail_Q s).val j z=0 from g,norm_zero,sum_const_zero]; norm_num
end YM.CF.QuadClock

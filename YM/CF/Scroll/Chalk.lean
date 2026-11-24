import YM.CF.Scroll.Hud
import YM.CF.Mir.Spin
import YM.CF.Dial.Chair
set_option autoImplicit false
noncomputable section
namespace YM.CF.Scroll
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators
attribute [local instance] opCStarAlgebra
variable (p q r:Bool)(v:Signed)
def hush {α:Type*} [Neg α](p:Bool)(x:α):α:= if p then -x else x
@[simp] lemma hush_false {α:Type*}[Neg α](x:α):hush false x=x:=rfl
@[simp] lemma hush_true {α:Type*}[Neg α](x:α):hush true x= -x:=rfl
lemma hush_comp {α:Type*}[InvolutiveNeg α](x:α) : hush p (hush q x) = hush (p.xor q) x:=by cases p<;>cases q<;>simp

def cSignX(p:Bool)(x:ℂ):ℂ:=if p then star x else x
def windX {n:Type*}(p:Bool)(A:Op n): Op n:=if p then cc A else A
variable {n:Type*}[Fintype n][DecidableEq n](A B:Op n)
def sings (p:Bool)(U:UNI n): Op n→Op n:=by exact fun X=> twist U (windX p X) -- def
@[simp] lemma sin_add(X Y:ℂ):cSignX p (X+Y)=cSignX p X+cSignX p Y:=by cases p<;>simp [cSignX]
@[simp] lemma win_a:windX p (A+B)=windX p A+windX p B:=by cases p<;>simp [windX]
@[simp] lemma win_n:windX p (-A)= -windX p A:=by cases p<;>simp [windX]
@[simp] lemma win_l:windX p (A-B)=windX p A-windX p B:=by cases p<;>simp [windX]
@[simp] lemma win_m:windX p (A*B)=windX p A*windX p B:=by cases p<;>simp [windX]
@[simp] lemma win_s:windX p (star A)=star (windX p A):=by cases p<;>simp [windX]
@[simp] lemma win_c(z:ℂ):windX p (z • A)= cSignX p z • windX p A:=by cases p<;>simp [windX,cSignX]
@[simp] lemma win_r(z:ℝ):windX p (z • A)= z • windX p A:=by cases p<;>simp [windX]
lemma win_sum {I:Type*}(s:Finset I)(A:I→Op n):windX p (∑ i∈s,A i)=∑ i∈s,windX p (A i):=by cases p<;>ext i j<;>simp [windX,Matrix.sum_apply]
lemma win_z:windX p (0:Op n)=0:=by cases p<;>simp [windX]
lemma win_i:windX p (1:Op n)=1:=by cases p<;>simp [windX]
@[simp] lemma typ_l : Continuous (windX (n:=n) p) := by cases p; exact continuous_id; exact cc_cont
@[simp] lemma singT (U:UNI n)(A:Op n): sings p U A = twist U (windX p A):=rfl
lemma win_trace : (windX p A).trace=cSignX p (Matrix.trace A):=by cases p<;> simp [windX,cSignX,Matrix.trace,star_sum,Matrix.diag_apply]
lemma sings_sumts {I:Type*}(U:UNI n)(A:I→Op n)(h: Summable A): sings p U (∑' i,A i)=∑' i, sings p U (A i):=by
 let V:= sings p U; let H:= h.hasSum; have he: Continuous V:= (breeze _).comp (typ_l p); refine Eq.symm (HasSum.tsum_eq (show HasSum (fun i=>V (A i)) (V _) from ?_)); have hx:= (he.continuousAt (x:=∑' i,A i)).tendsto.comp H; have hw(s:Finset I) : V (∑ i∈s,A i)=∑ i∈s,V (A i):=by unfold V; simp only [singT,win_sum,map_sum]
 exact hx.congr (fun s=>hw s)
structure JetS (s:Signed)(p r:Bool) (A:UNI SpinIdx):Prop where
  cliff i:sings p A (gammaOp (s.perm i))=hush (s.flip i) (gammaOp i)
  grade :sings p A grading=hush r grading
  justice:A.val*spinJ=spinJ*cc A.val -- from real J 
-- Need genesis and ordering using generators
lemma calmSX: JetS 1 false false 1:=⟨fun i=> Fock.one_des _, Fock.one_des _,by simp⟩
lemma cloneSX: JetS 1 true false ⟨spinJ,spinJ_unitary⟩:=by refine ⟨fun i=> Mir.twist_comm _ _ _ (spinJ_inter i).symm,Mir.twist_comm _ _ _ spinJ_grading.symm,?_⟩; simp [spinJ_real]
lemma mirrorX (i:Axis) : JetS (Signed.mirror i) false true ⟨Mir.pin i,Mir.pin_U i⟩:=by -- imports
 refine ⟨fun j=> ?_,?_,?_⟩
 · by_cases h:i=j; subst j; rw [show (Signed.mirror i).flip i=true from by simp [Signed.mirror],hush_true]; apply Mir.twist_comm; change Mir.pin i*gammaOp i= -(gammaOp i)*Mir.pin i; unfold Mir.pin; rw [mul_assoc,gradingSwap,mul_neg,neg_mul]
   rw [show (Signed.mirror i).flip j=false from by simp [Signed.mirror,h]]; apply Mir.twist_comm; change Mir.pin i * gammaOp j=_*Mir.pin i; unfold Mir.pin; rw [mul_assoc,gradingSwap,mul_neg,←mul_assoc,gammaSwap i j h,neg_mul,neg_neg,mul_assoc]; rw [hush_false]
 · apply Mir.twist_comm; change Mir.pin i * grading= (-grading)*Mir.pin i; unfold Mir.pin; rw [neg_mul,←mul_assoc,gradingSwap,neg_mul,neg_neg]
 unfold Mir.pin; change (_*_)*_=spinJ* _; rw [mul_assoc,spinJ_grading,← mul_assoc,spinJ_inter,cc_mul,mul_assoc]
end YM.CF.Scroll

import YM.CF.Urn.Ione
import YM.CF.Urn.Shaft
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Urn
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Proa
variable {I α ι n m: Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m][LinearOrder ι][Fintype ι]
open Stilo Scree Hake
open Pastry
-- rectangular linear colors
variable (b r t:Bool)(U:UNI n)(V:UNI m)
lemma snowComp (b r:Bool)(x) : cSignX r (cSignX b x)=cSignX (b.xor r) x:=by cases b<;> cases r<;>simp [cSignX]
def windV (b:Bool)(X:Matrix n m ℂ):Matrix n m ℂ:= X.map (cSignX b)
lemma wru (b r:Bool)(X:Matrix n m ℂ): windV r (windV b X)= windV (b.xor r) X:= Matrix.ext fun i j=> snowComp b r _
lemma wun (t:Bool)(U:Op n):windV t U=windX t U:=by cases t<;>rfl
lemma wum(t:Bool)(A:Matrix n m ℂ)(B:Matrix m ι ℂ): windV t (A*B)=windV t A*windV t B:=by cases t <;> ext i j <;> simp [windV,cSignX,mul_apply,star_sum]
lemma filmG(U:UNI n):(invFilm U).val=Complex.I • U.val:=by unfold invFilm; change (Complex.I • 1)*_= _; rw [Algebra.smul_mul_assoc,one_mul]
abbrev grainL (r:Bool)(U:UNI n):UNI n:= if r then invFilm U else U
def suburban (X:Matrix n m ℂ):Matrix n m ℂ:= U.val*windV b X*star V.val
lemma duel (X:Matrix n m ℂ): (grainL r U).val*windV b X*star (grainL r V).val=suburban b U V X:=by
 cases r; rfl
 unfold suburban; simp only [grainL,ite_true,filmG,Matrix.smul_mul,star_smul,Matrix.mul_smul,smul_smul]; simp
lemma weaveR(t:Bool)(U:UNI n): (thread U t).valᵀ=star (windV t U.val):=by cases t <;> ext i j <;> simp [thread,windV,ccU,cSignX,cc_apply]
lemma weaveS(t:Bool)(U:UNI n): (thread U t).valᵀ=windV t (star U.val):=by rw [weaveR,wun,wun, win_s]
lemma link_o (X X':Matrix n m ℂ)(h:X'=suburban b U V X) : (crib U r t).valᵀ*windV (t.xor r) X'=windV (b.xor r) (windV t X) * (crib V r t).valᵀ:=by
 unfold crib; let A:=grainL r U; let C:=grainL r V; let u:= t.xor r
 change (thread A u).valᵀ*windV u X'=windV _ _*(thread C u).valᵀ; rw [weaveS,weaveS,←wum]
 rw [h,←duel b r U V X]; change windV u (star A.val * (A.val * _*star C.val))= _
 rw [←Matrix.mul_assoc,←Matrix.mul_assoc (star _), A.property.1,Matrix.one_mul,wum]; congr 1; rw [wru,wru]; congr 1; cases b<;>cases r<;>cases t<;>rfl
lemma link_l (X X':Matrix n m ℂ)(h:X'=suburban b U V X)(i:n)(j:m): ∑ k,(crib U r t).val k i * cSignX (t.xor r) (X' k j)= ∑ k, cSignX (b.xor r) (cSignX t (X i k))* (crib V r t).val j k:=Matrix.ext_iff.mpr (link_o b r t U V _ _ h) i j
lemma link_b (t t' b r:Bool)(p:t ≠ t')(K:UNI m) : thread (grainL r K) (t'.xor r)=ccU (crib K r t):= by apply Subtype.ext; cases t <;> cases t' <;> cases r <;> first| contradiction| rfl| ext i j'; simp [thread,ccU,crib,grainL] -- tune
lemma link_p (t':Bool)(p:t ≠ t')(X Y:Op n)(h:Y=sings b U X): windV (b.xor r) (windV t X)=(crib U r t).valᵀ*windV (t.xor r) Y *(crib U r t').val:=by
 rw [link_o b r t U U X Y (by rw [h,singT, twist_formula,suburban,wun]),mul_assoc]; nth_rw 1 [show crib U r t'= thread (grainL r U) (t'.xor r) from rfl]; rw [link_b _ _ b r p]
 let P:=ccU (crib U r t); rw [show (crib U r t).valᵀ=star P.val from ?_, P.property.1,mul_one]; ext i j; simp [P,ccU] -- tune
lemma link_k (t':Bool)(p:t ≠t')(X Y:Op n)(h:Y=sings b U X)(i j:n):cSignX (b.xor r) (cSignX t (X i j))=∑ k:n,∑ l:n,(crib U r t).val k i * (crib U r t').val l j*cSignX (t.xor r) (Y k l):=by
 change windV _ (windV _ X) i j=_; rw [link_p b r t U _ p X Y h, mul_assoc, Matrix.mul_apply]; apply sum_congr rfl; intro k _; rw [Matrix.mul_apply,mul_sum]; refine sum_congr rfl fun l _=>?_ ; simp [windV,mul_assoc,mul_comm,mul_left_comm]
end YM.CF.Urn

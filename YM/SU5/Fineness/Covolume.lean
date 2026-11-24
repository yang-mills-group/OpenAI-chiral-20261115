import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic
/-!
# Toolkit for correctly compensating the scale-by-scale offset of the physical theory

The precision matrices are singular both from gauge modes and from harmonic modes, with
Lebesgue normalization on the quotient specified by coordinates on those zero modes. Carry
*exactly* the basis of omitted modes through all the changes of variables.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.Fineness
open Function Matrix
open scoped Matrix
-- intentionally not root level abbreviations Mat etc
abbrev Tab (I J : Type*) := Matrix I J ℝ
abbrev Sheet (I : Type*) := Matrix I I ℝ
variable {I J K L p q : Type*} [DecidableEq I] [Fintype I] [DecidableEq J] [Fintype J]
   [DecidableEq K][Fintype K] [DecidableEq L][Fintype L] [DecidableEq p][Fintype p]
variable {A : Sheet I} {B : Sheet K} {X : Tab I J} {Y : Tab K L}

/-- Null columns have a left inverse. *Not* yet asserting non-singularity of the precision on the slice. -/
def Rail (X : Tab I J) := ∃ R : Tab J I, R * X = 1
structure ZeroBasis (A : Sheet I) (X : Tab I J) : Prop where
 symmA : Aᵀ=A
 nullA : A*X=0
 rail : Rail X

def axes (X : Tab I J) : Tab J I := by
  classical
  exact if h : Rail X then h.choose else 0
def torsion (A : Sheet I) (X : Tab I J) : ℝ:= (A+(axes X)ᵀ*axes X).det
lemma axes_deck (h : Rail X) : axes X*X=1:=by unfold axes; rw [dif_pos h]; exact h.choose_spec
namespace ZeroBasis
variable (h : ZeroBasis A X)
include h
lemma turnA : Xᵀ*A=0:=by nth_rw 1 [← h.symmA]; rw [← transpose_mul,h.nullA]; rfl
lemma reels {R : Tab J I} (r : R*X=1) : torsion A X=(A+Rᵀ*R).det:= by
  let D:=axes X; let Z:= R-D; let T:Sheet I:=1+X*Z
  have hu : D*X=1:=axes_deck h.rail
  have hv : Z*X=0:=by rw [show Z=R-D from rfl, Matrix.sub_mul,r,hu,sub_self]
  have ht : T.det=1:= by dsimp only [T]; rw [det_one_add_mul_comm,hv,add_zero,det_one]
  have he:D*T=R:=by unfold T; rw [Matrix.mul_add,Matrix.mul_one, ← Matrix.mul_assoc,hu,Matrix.one_mul]; unfold Z; abel
  have hs: A*T=A:=by unfold T; rw [Matrix.mul_add,Matrix.mul_one,←Matrix.mul_assoc,h.nullA]; simp
  have hx:Tᵀ*A=A:=by nth_rw 1 [←h.symmA]; rw [← transpose_mul,hs,h.symmA]
  have hp : Tᵀ*(A+Dᵀ*D)*T=A+Rᵀ*R:=by
    rw [Matrix.mul_add Tᵀ A, Matrix.add_mul, hx, hs,←Matrix.mul_assoc Tᵀ, ← transpose_mul, he, Matrix.mul_assoc,he]
  rw [←hp,det_mul,det_mul,det_transpose,ht,one_mul,mul_one]; rfl

/-- Nonsingular coordinate substitution with squared Jacobian, available even from another
    index set. -/
lemma petition {Y0 : Tab K J} (T : Tab I K) (U : Tab K I) (f : T*Y0=X)
    (v : T*U=1) (t : U*T=1) : ZeroBasis (Tᵀ*A*T) Y0:= by
  let D:=axes X; let m:=D*T
  constructor
  · rw [transpose_mul,transpose_mul,h.symmA,transpose_transpose,Matrix.mul_assoc]
  · rw [Matrix.mul_assoc,f,Matrix.mul_assoc,h.nullA]; simp
  exact ⟨m,by unfold m; rw [Matrix.mul_assoc,f]; exact axes_deck h.rail⟩

omit h in
lemma factors (T : Tab K I) (U : Tab I K) (e : I ≃ K) (R : Sheet K) :
   (U*R*T).det=(U*T).det* R.det := by
  let U':= U.submatrix id e; let T':= T.submatrix e id; let R':=R.submatrix e e
  rw [show U*R*T=U'*R'*T' from ?_,show U*T=U'*T' from ?_, ← det_submatrix_equiv_self e R]; swap
  · exact congrArg id (by unfold U' T'; rw [submatrix_mul_equiv]; rfl) -- adjust
  · rw [det_mul,det_mul,det_mul]; unfold R'; ring
  unfold U' R' T'; rw [submatrix_mul_equiv,submatrix_mul_equiv]; rfl

lemma resize {Y0 : Tab K J} (T : Tab I K) (U : Tab K I) (e : K ≃ I)
    (f : T*Y0=X)(v:T*U=1)(t:U*T=1) : torsion (Tᵀ*A*T) Y0=(Tᵀ*T).det*torsion A X:=by
  let D:=axes X; have hx: D*T*Y0=1:= by rw [Matrix.mul_assoc,f]; exact axes_deck h.rail
  rw [(h.petition T U f v t).reels hx,show Tᵀ*A*T+(D*T)ᵀ*(D*T)=Tᵀ*(A+Dᵀ*D)*T from ?_]
  · exact factors T Tᵀ e (A+Dᵀ*D)
  rw [transpose_mul,Matrix.mul_add,Matrix.add_mul]; simp only [Matrix.mul_assoc]

lemma slide_basis {Z : Tab I K} (T : Tab J K) (U : Tab K J) (v:T*U=1)(t:U*T=1) (a:X*T=Z) : ZeroBasis A Z:=by
  subst Z; refine ⟨h.symmA,?_,U*axes X,?_⟩
  · rw [←Matrix.mul_assoc,h.nullA,Matrix.zero_mul]
  rw [Matrix.mul_assoc,←Matrix.mul_assoc (axes X),axes_deck h.rail,Matrix.one_mul,t]

lemma basis_expense {Z : Tab I K} (e : J ≃ K) (T : Tab J K) (U : Tab K J)
    (v:T*U=1)(t:U*T=1)(a:X*T=Z): torsion A X=(T*Tᵀ).det * torsion A Z := by
  subst Z; let R:= U*axes X; have hR:R*(X*T)=1:=by unfold R; rw [Matrix.mul_assoc, ←Matrix.mul_assoc (axes X),axes_deck h.rail,Matrix.one_mul,t]
  let D:=axes X; have hB:D*X=1:=axes_deck h.rail
  rw [h.reels hB,(h.slide_basis T U v t rfl).reels hR]
  -- domain det of shear making RX effect. Use D transpose with multiplier U need square U reindex, or general Woodbury weighing positive UU
  let L':=T*Tᵀ; let G:=1+X*(L'-1)*D -- transforms A to itself, R λν
  have hL:L'*(Uᵀ*U)=1:= by
    calc _= T*(Tᵀ*Uᵀ)*U := by simp only [Matrix.mul_assoc,L']
         _=1:=by rw [← transpose_mul,t,transpose_one]; simpa using v
  have hK:Gᵀ*A=A:=by rw [show G=1+_ from rfl,transpose_add,transpose_mul,transpose_mul,transpose_one,Matrix.add_mul,Matrix.one_mul,Matrix.mul_assoc, Matrix.mul_assoc _ Xᵀ A,h.turnA]; simp
  have hz:D*G=L'*D:=by unfold G; rw [Matrix.mul_add,Matrix.mul_one,← Matrix.mul_assoc, ← Matrix.mul_assoc,hB, Matrix.one_mul, Matrix.sub_mul,Matrix.one_mul]; abel
  have he:Gᵀ*Rᵀ*R=Dᵀ*D:=by
    change Gᵀ*(U*D)ᵀ*(U*D)=_
    rw [transpose_mul, ←Matrix.mul_assoc Gᵀ, ←transpose_mul D G, hz, transpose_mul, show L'ᵀ=L' by unfold L'; simp]
    rw [show Dᵀ* L'* Uᵀ * (U*D) =Dᵀ*(L'*(Uᵀ*U))*D from by simp only [Matrix.mul_assoc], hL,Matrix.mul_one]
  rw [show A+Dᵀ*D= Gᵀ*(A+Rᵀ*R) by rw [Matrix.mul_add,hK,← Matrix.mul_assoc Gᵀ,he],det_mul,det_transpose]
  have hv: G.det=L'.det:=by unfold G; rw [Matrix.mul_assoc,det_one_add_mul_comm,Matrix.mul_assoc,hB,Matrix.mul_one]; congr 1; abel
  rw [hv]

section
lemma split_right (B:Sheet K)(p:Bᵀ=B) : ZeroBasis (fromBlocks A 0 0 B) (fromRows X 0):= by
 constructor
 · rw [fromBlocks_transpose]; simp [h.symmA,p]
 · rw [fromBlocks_mul_fromRows]; simp [h.nullA]
 exact ⟨fromCols (axes X) 0,by rw [fromCols_mul_fromRows]; simp [axes_deck h.rail]⟩
lemma right_bill (B:Sheet K)(p:Bᵀ=B) : torsion (fromBlocks A 0 0 B) (fromRows X 0)=torsion A X * B.det:=by
 let D:=axes X; have hp:(fromCols D (0:Tab J K))*(fromRows X (0:Tab K J))=1:=by rw [fromCols_mul_fromRows]; simp only [Matrix.zero_mul,add_zero,axes_deck h.rail,D]
 rw [(h.split_right B p).reels hp,transpose_fromCols,fromRows_mul_fromCols,fromBlocks_add]; simp only [transpose_zero,Matrix.zero_mul,Matrix.mul_zero,add_zero]; rw [det_fromBlocks_zero₁₂]; rfl
lemma split_left (B:Sheet K)(p:Bᵀ=B) : ZeroBasis (fromBlocks B 0 0 A) (fromRows 0 X):=by
 constructor
 · rw [fromBlocks_transpose]; simp [h.symmA,p]
 · rw [fromBlocks_mul_fromRows]; simp [h.nullA]
 exact ⟨fromCols 0 (axes X),by rw [fromCols_mul_fromRows]; simp [axes_deck h.rail]⟩
lemma left_bill (B:Sheet K)(p:Bᵀ=B) : torsion (fromBlocks B 0 0 A) (fromRows 0 X)= B.det*torsion A X:=by
 let D:=axes X; have hp:(fromCols (0:Tab J K) D)*(fromRows (0:Tab K J) X)=1:=by rw [fromCols_mul_fromRows]; simp [axes_deck h.rail,D]
 rw [(h.split_left B p).reels hp,transpose_fromCols,fromRows_mul_fromCols, fromBlocks_add]; simp only [transpose_zero,Matrix.zero_mul,Matrix.mul_zero,add_zero]; rw [det_fromBlocks_zero₁₂]; rfl
lemma joint_basis (k:ZeroBasis B Y) : ZeroBasis (fromBlocks A 0 0 B) (fromBlocks X 0 0 Y):=by
 constructor
 · rw [fromBlocks_transpose]; simp [h.symmA,k.symmA]
 · rw [fromBlocks_multiply]; simp [h.nullA,k.nullA]
 exact ⟨fromBlocks (axes X) 0 0 (axes Y),by rw [fromBlocks_multiply]; simp [axes_deck h.rail,axes_deck k.rail,fromBlocks_one]⟩
lemma joint_bill (k:ZeroBasis B Y) : torsion (fromBlocks A 0 0 B) (fromBlocks X 0 0 Y)=torsion A X*torsion B Y:=by
 let R:=axes X; let S:=axes Y
 have hp:(fromBlocks R 0 0 S)*(fromBlocks X 0 0 Y)=1:=by rw [fromBlocks_multiply]; simp [axes_deck h.rail,axes_deck k.rail,fromBlocks_one,R,S]
 rw [(h.joint_basis k).reels hp,fromBlocks_transpose,fromBlocks_multiply, fromBlocks_add]; simp only [transpose_zero,Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add]; rw [det_fromBlocks_zero₁₂]; rfl
omit h in
lemma filled (I:Type*)[Fintype I][DecidableEq I]:ZeroBasis (0:Sheet I) (1:Sheet I):=⟨by simp, Matrix.zero_mul _, 1,Matrix.one_mul _⟩
omit h in
lemma paid (I:Type*)[Fintype I][DecidableEq I]: torsion (0:Sheet I) (1:Sheet I)=1:=by rw [(filled I).reels (Matrix.one_mul (1:Sheet I))]; simp
end
end ZeroBasis
end YM.Fineness
#print axioms YM.Fineness.ZeroBasis.left_bill
#print axioms YM.Fineness.ZeroBasis.basis_expense
#print axioms YM.Fineness.ZeroBasis.resize

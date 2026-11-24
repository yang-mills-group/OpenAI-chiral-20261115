import YM.CF.Matter.PairGauge

/-! Pairing map normalization at e₀. The matrix is a **signed** permutation;
use a sparse computable presentation over ℤ for the finite checks. -/
set_option autoImplicit false
namespace YM.CF.SU.Pair
open Finset ExTwo
open scoped Matrix BigOperators
noncomputable def e0 : V := basisVec (0:F)
def zbasis (i : F) (j : F) : ℤ := if j=i then 1 else 0

def lapZ : (k : ℕ) → Matrix (Fin k) (Fin k) ℤ → ℤ
| 0,_ => 1
| k+1,A => ∑ i, if A 0 i=0 then 0 else (-1)^i.val*A 0 i * lapZ k (A.submatrix Fin.succ i.succAbove)
lemma lapZ_eq (k : ℕ) (A) : lapZ k A = A.det := by
  induction k with
  | zero => rw [lapZ,Matrix.det_isEmpty]
  | succ k ih =>
    rw [lapZ,Matrix.det_succ_row_zero]
    apply sum_congr rfl; intro i _; split
    · rename_i e; simp [e]
    rw [ih]
def epsZ (p q : Ten) := Matrix.of ![zbasis p.val.1,zbasis p.val.2,zbasis q.val.1, zbasis q.val.2,zbasis 0]
lemma zbasis_cast (i j : F) : ((zbasis i j : ℤ):ℂ)=basisVec i j := by by_cases h:j=i <;> simp [zbasis,h,basisVec]
lemma epsN (p q : Ten) : ((lapZ 5 (epsZ p q):ℤ):ℂ)= eps e0 p q := by
  rw [lapZ_eq]; change (Int.castRingHom ℂ) _ = Matrix.det (rows (basisVec p.val.1) (basisVec p.val.2) (basisVec q.val.1) (basisVec q.val.2) e0)
  rw [RingHom.map_det]
  congr 1; ext i j
  fin_cases i <;> exact zbasis_cast _ _

def seedN : Matrix Sheet Sheet ℤ :=
  let Q : Matrix Ten Ten ℤ := Matrix.of fun i j => lapZ 5 (epsZ i j)
  let M : Matrix Ten F ℤ := Matrix.of fun i j => zbasis 0 i.val.1 * zbasis j i.val.2-zbasis 0 i.val.2 * zbasis j i.val.1
  let W : Matrix F F ℤ := Matrix.of fun i j => -(zbasis 0 i * zbasis 0 j)
  Matrix.fromBlocks Q M Mᵀ W
lemma seed_eq (x y:Sheet) : ((seedN x y:ℤ):ℂ)=pairM e0 x y := by
  rcases x with x|x <;> rcases y with y|y
  · change _=cc _ _ _; rw [cc_apply, ← epsN]; simp [seedN]
  · change (((zbasis _ _ * zbasis _ _ - zbasis _ _ * zbasis _ _):ℤ):ℂ)= mix _ _ _
    simp only [Int.cast_mul,Int.cast_sub,zbasis_cast]; rfl
  · change (((zbasis _ _ * zbasis _ _ - zbasis _ _ * zbasis _ _):ℤ):ℂ)= mix _ _ _
    simp only [Int.cast_mul,Int.cast_sub,zbasis_cast]; rfl
  change ((-(zbasis 0 x * zbasis 0 y) : ℤ):ℂ)= -((star e0 x)*(star e0 y))
  push_cast; simp [e0,← zbasis_cast]

def p (i j:F) (h:i<j := by decide) : Sheet := .inl ⟨(i,j),h⟩
def f (i:F) : Sheet := .inr i

def northPerm : Equiv.Perm Sheet :=
  Equiv.swap (p 0 1) (f 1)*Equiv.swap (p 0 2) (f 2)*Equiv.swap (p 0 3) (f 3)*Equiv.swap (p 0 4) (f 4) *
    Equiv.swap (p 1 2) (p 3 4) * Equiv.swap (p 1 3) (p 2 4) * Equiv.swap (p 1 4) (p 2 3)
def coloration (x:Sheet) : ℤ := if x∈({(p 1 3),p 2 4,f 0} : Finset Sheet) then -1 else 1
set_option maxRecDepth 16000 in
set_option maxHeartbeats 1000000 in
lemma seed_switch : ∀ i j, seedN i j = if northPerm i = j then coloration j else 0 := by
  decide +kernel
lemma colorCase (i j:Sheet) : pairM e0 i j = if northPerm i=j then (coloration j:ℂ) else 0 := by rw [← seed_eq,seed_switch]; split <;> simp
lemma invol : ∀ i, northPerm (northPerm i)=i := by decide
lemma same_color : ∀ i, coloration (northPerm i)=coloration i := by decide
lemma prod_color : (∏ i, coloration i)= -1 := by decide
lemma perm_parity : northPerm.sign= -1 := by
  simp only [northPerm,map_mul]
  iterate 7 rw [Equiv.Perm.sign_swap (by decide)]
  decide
lemma symmetric : (pairM e0)ᵀ = pairM e0 := by
  ext i j; rw [Matrix.transpose_apply,colorCase,colorCase]
  by_cases h:northPerm i=j
  · subst j; rw [if_pos (invol _),if_pos rfl,same_color]
  rw [if_neg h,if_neg (show northPerm j≠i from fun e => h (by rw [← e,invol]))]
lemma northStar : star (pairM e0) = pairM e0 := by
  ext i j; change star (pairM e0 j i)=_; rw [show pairM e0 j i=pairM e0 i j from Matrix.ext_iff.mpr symmetric i j,colorCase]; split <;> simp only [star_zero,star_intCast]
lemma northSq : pairM e0*pairM e0=1 := by
  ext i j; rw [Matrix.mul_apply,sum_eq_single (northPerm i)]
  · rw [colorCase,colorCase,invol,same_color]; by_cases e:i=j
    · subst j; simp only [ite_true, Matrix.one_apply_eq]; rw [← Int.cast_mul,
        show coloration i*coloration i=1 by unfold coloration; split <;> norm_num, Int.cast_one]
    rw [if_neg e, mul_zero]; exact (Matrix.one_apply_ne e).symm
  · intro a _ ha; rw [colorCase,if_neg (Ne.symm ha),zero_mul]
  simp
lemma northU : pairM e0 ∈ unitary _ := by constructor <;> rw [northStar,northSq]
lemma northOrientation : (pairM e0).det=1 := by
  rw [show pairM e0 = (Matrix.diagonal fun x=> (coloration x:ℂ)).submatrix northPerm id by
    ext i j; rw [colorCase]; split <;> rename_i h <;> simp [h]]
  rw [Matrix.det_permute,perm_parity,Matrix.det_diagonal,← Int.cast_prod,prod_color]; norm_num
end YM.CF.SU.Pair

import YM.CF.Matter.Form
/-!
An explicit equivariant pairing matrix using the fundamental unit sphere.
Using the five-connected pairing-space idea, for these
representations we can avoid even neutral auxiliary colors. It is not a
mass for physical slots! This is intended for an orientation of the
cutoff determinant line.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
noncomputable section
namespace YM.CF.SU.Pair
open ExTwo Finset
open scoped Matrix BigOperators Kronecker
abbrev V := F → ℂ

def rows (x y v w u : V) : Op F := Matrix.of ![x,y,v,w,u]
def eps (u:V) : Op Ten := Matrix.of fun p q =>
    (rows (basisVec p.val.1) (basisVec p.val.2) (basisVec q.val.1) (basisVec q.val.2) u).det

lemma rows_up (a b c d u x y v w : V) :
    ((rows a b v w u).updateRow 0 x).updateRow 1 y=rows x y v w u ∧
    ((rows x y c d u).updateRow 2 v).updateRow 3 w=rows x y v w u := by
  constructor <;> ext i j <;> fin_cases i <;> rfl
lemma expand_eps (x y v w u : V) : (rows x y v w u).det =
    ∑ p:Ten, ∑ q:Ten, exterior x y p * exterior v w q * eps u p q := by
  calc
    _ = ∑ p:Ten, exterior x y p * (rows (basisVec p.val.1) (basisVec p.val.2) v w u).det := by
      have he (a b:V) := (rows_up 0 0 0 0 u a b v w).1
      simpa only [he] using (twoRow (rows 0 0 v w u) (show (0:F)≠1 by decide) x y)
    _ = _ := by
      apply sum_congr rfl; intro p _
      let a := basisVec p.val.1; let b := basisVec p.val.2
      have he (c d:V) := (rows_up 0 0 0 0 u a b c d).2
      change _ * (rows a b v w u).det = _
      have hr := twoRow (rows a b 0 0 u) (show (2:F)≠3 by decide) v w
      simp only [he] at hr; rw [hr, mul_sum]; apply sum_congr rfl; intro q _
      rw [mul_assoc]; rfl
lemma through (x y v w u : V) (A : Op F) : rows x y v w u * Aᵀ =
    rows (A *ᵥ x) (A *ᵥ y) (A *ᵥ v) (A *ᵥ w) (A *ᵥ u) := by
  ext i j; rw [Matrix.mul_apply]; simp only [rows,Matrix.of_apply,Matrix.transpose_apply]
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,mul_comm]
lemma eps_formula (A : Op F) (u:V) : (wedgeOp A)ᵀ*eps (A *ᵥ u)*wedgeOp A = A.det • eps u := by
  ext p q
  let x := basisVec p.val.1; let y := basisVec p.val.2; let v := basisVec q.val.1; let w := basisVec q.val.2
  have ht : ∀ p : Ten, exterior (A *ᵥ basisVec p.val.1) (A *ᵥ basisVec p.val.2) = (wedgeOp A).col p := by
    intro p; rw [← exterior_action, exterior_basis, Matrix.mulVec_single_one]
  change _ = A.det * (rows x y v w u).det
  rw [mul_comm A.det, ← Matrix.det_transpose A, ← Matrix.det_mul, through,expand_eps]
  dsimp only [x,y,v,w]; rw [ht p,ht q]; simp only [Matrix.mul_apply, Matrix.transpose_apply,sum_mul, Matrix.col_apply]
  rw [sum_comm]
  apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; ring

/-- Map w ↦ u ∧ w. -/
def mix (u:V) : Matrix Ten F ℂ := Matrix.of fun i j => exterior u (basisVec j) i
lemma mix_vec (x v:V) : mix x *ᵥ v=exterior x v := by
  funext p; simp [Matrix.mulVec,dotProduct,mix,exterior,basisVec,Pi.single_apply, mul_ite,_root_.sub_mul,sum_sub_distrib]
lemma mix_formula (A : Op F) (u:V) : wedgeOp A * mix u=mix (A *ᵥ u)*A := by
  ext p q
  have hh (B : Matrix Ten F ℂ) : B p q = (B *ᵥ Pi.single q 1) p := by rw [Matrix.mulVec_single_one]; rfl
  rw [hh (wedgeOp A*mix u)]
  have he := exterior_action A u (basisVec q)
  change _ = (mix _ * A) p q
  calc
    _ = (exterior (A*ᵥ u) (A*ᵥ basisVec q)) p := by rw [← Matrix.mulVec_mulVec,mix_vec, ← he]; rfl
    _ = _ := by rw [← mix_vec,Matrix.mulVec_mulVec]; unfold basisVec; rw [Matrix.mulVec_single_one]; rfl
lemma cc_vec (A : Op F) (u:V) : star (A *ᵥ u)=cc A *ᵥ star u := by
  funext i; simp [Matrix.mulVec,dotProduct,star_sum]
def lone (u:V) := -(Matrix.vecMulVec (star u) (star u) : Op F)
lemma lone_formula (A : Op F) (u:V) : cc A * lone u * (cc A)ᵀ=lone (A*ᵥ u) := by
  simp only [lone,_root_.mul_neg,_root_.neg_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, cc_vec]

def pairM (u:V) : Op Sheet := Matrix.fromBlocks (cc (eps u)) (mix u) (mix u)ᵀ (lone u)
lemma pairM_cong (g:E) (u:V) :
    pairM ((fund g)*ᵥ u) = each (fund g) * pairM u * (each (fund g))ᵀ := by
  let A := fund g
  let W := wedgeOp A
  have he := eps_formula A u
  rw [show Matrix.det A=1 from fund_det _,one_smul] at he
  have hv : W * star W = 1 := (wedge_mem (fund_U g)).2
  have hm : cc (eps (A *ᵥ u))= W*cc (eps u)*Wᵀ := by
    rw [← he]
    change _ = W*cc (Wᵀ*eps (A*ᵥ u)*W)*Wᵀ
    rw [cc_mul,cc_mul, show cc Wᵀ=star W from rfl]
    have hy : cc W * Wᵀ=1 := by rw [cc, ← Matrix.transpose_mul, hv,Matrix.transpose_one]
    simp only [mul_assoc, hy,mul_one, ← mul_assoc W (star W),hv,one_mul]
  have hA : A * star A = 1 := (fund_U g).2
  have hh : W*mix u*(cc A)ᵀ=mix (A*ᵥ u) := by
    rw [show W*mix u=mix (A*ᵥ u)*A from mix_formula ..,Matrix.mul_assoc,
      show (cc A)ᵀ=star A from rfl,hA,Matrix.mul_one]
  have ht := congrArg Matrix.transpose hh
  rw [Matrix.transpose_mul, Matrix.transpose_transpose,Matrix.transpose_mul,← Matrix.mul_assoc] at ht
  change pairM (A*ᵥ u)=each A*pairM u*(each A)ᵀ
  simp only [pairM,each,Join.both,Matrix.fromBlocks_multiply,Matrix.fromBlocks_transpose]
  simp only [Matrix.transpose_zero,Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add]
  -- adjust simp ordering
  rw [hm,show wedgeOp A=W from rfl,hh,ht,lone_formula]
end YM.CF.SU.Pair

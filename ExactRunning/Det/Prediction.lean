import ExactRunning.Det.Schur
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Restricted determinants: split at prediction

Second splitting of the joint cost. Algebraic theorem, to be used when
coarse background equals its prediction, so the joint Hessian contains
a penalty factorized through the first derivative of coarse deviation.
Cost on the extended system (fine links u, frame f, coarse links v)
then reduces to cost on fine links plus a `K` term. Here M effects coarse
gauge motion and (U, M) is the derivative of prediction. With coarse
gauge completion M Mᵀ, choosing coordinates
u, y = Mᵀv, w = v-Uu-Mf
diagonalizes formally (Gram identity `u_y_w_gram` regardless of degeneracy).
Compute restricted log determinants using `Fit`; Jacobian (squared)
pays for coarse ghost `MᵀM`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Matrix Filter
open scoped Topology ContDiff

namespace ExactRunning

variable {m n k j : Type} [Fintype m] [Fintype n] [Fintype k] [Fintype j]
  [DecidableEq m] [DecidableEq n] [DecidableEq k] [DecidableEq j]

variable {P : ModeCut m} {Q : ModeCut n} {R : ModeCut k}

lemma Fit.rows {A : ℝ → Matrix m k ℝ} {B : ℝ → Matrix n k ℝ}
    (ha : Fit P R A) (hb : Fit Q R B) :
    Fit (P.direct Q) R (fun t => fromRows (A t) (B t)) where
  cont
    | .inl a,_ => ha.cont a _
    | .inr a,_ => hb.cont a _
  van := by
    simp only [ModeCut.direct_e, fromBlocks_mul_fromRows, fromRows_mul,Matrix.zero_mul,add_zero,zero_add]
    rintro (a|a) b
    · exact ha.van a b
    exact hb.van a b

lemma Fit.cols {A : ℝ → Matrix k m ℝ} {B : ℝ → Matrix k n ℝ}
    (ha : Fit R P A) (hb : Fit R Q B) :
    Fit R (P.direct Q) (fun t => fromCols (A t) (B t)) := by
  simpa only [transpose_fromRows, transpose_transpose] using (ha.tr.rows hb.tr).tr

namespace Det

def predicted (F : Matrix m m ℝ) (U : Matrix k m ℝ) (M : Matrix k n ℝ) (K : Matrix k k ℝ) :=
  let A := fromCols U M
  fromBlocks
    (fromBlocks F (0:Matrix m n ℝ) 0 0 + Aᵀ * K * A)
    (-(Aᵀ * K))
    (-(K * A))
    (K + M * Mᵀ)

/-- Coordinates on fluctuations at equal backgrounds:
u (fine), y (coarse gauge reading), w (difference). -/
def u_y_w (U : Matrix k m ℝ) (M : Matrix k n ℝ) :=
  fromBlocks
    (fromBlocks 1 (0:Matrix m n ℝ) 0 0)
    (fromRows 0 Mᵀ)
    (-(fromCols U M))
    (1 : Matrix k k ℝ)

lemma u_y_w_gram (F : Matrix m m ℝ) (U : Matrix k m ℝ) (M : Matrix k n ℝ) (K : Matrix k k ℝ) :
    (u_y_w U M)ᵀ * (fromBlocks (fromBlocks F 0 0 (1:Matrix n n ℝ)) 0 0 K) * (u_y_w U M) =
      predicted F U M K := by
  rw [predicted,u_y_w, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [transpose_neg,transpose_one,transpose_zero,fromBlocks_transpose,Matrix.mul_zero, Matrix.zero_mul,
    zero_add,add_zero,Matrix.one_mul,Matrix.mul_one, Matrix.neg_mul,Matrix.mul_neg,neg_neg,
    fromBlocks_multiply,transpose_fromRows,transpose_transpose,fromBlocks_mul_fromRows,
    fromCols_mul_fromBlocks, fromCols_mul_fromRows,fromRows_zero,fromCols_zero]
  rw [add_comm _ K]

variable {F : ℝ → Matrix m m ℝ} {U : ℝ → Matrix k m ℝ} {M : ℝ → Matrix k n ℝ} {K : ℝ → Matrix k k ℝ}

private lemma u_y_w_fit (hu : Fit R P U) (hm : Fit R Q M) :
    Fit ((P.direct Q).direct R) ((P.direct Q).direct R) (fun t => u_y_w (U t) (M t)) :=
  ((Fit.one _).blocks (Fit.zero _ _) (Fit.zero _ _) (Fit.zero _ _)).blocks
    ((Fit.zero _ _).rows hm.tr) (hu.cols hm).neg (Fit.one _)

private lemma u_y_w_det (hu : Fit R P U) (hm : Fit R Q M) :
    Touch (fun t => ((P.direct Q).direct R).cutdet (u_y_w (U t) (M t)))
      (fun t => Q.cutdet ((M t)ᵀ * M t)) := by
  let h := ((Fit.one (P.direct Q)).blocks (Fit.zero (P.direct Q) R) (hu.cols hm) (Fit.one R))
  let h := ((u_y_w_fit hu hm).cutdet_mul h).symm
  refine h.congr (Eventually.of_forall fun _ => by simp)
     (Eventually.of_forall fun _ => ?_)
  dsimp only [u_y_w]
  simp only [fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,Matrix.mul_one,Matrix.one_mul,
    zero_add,add_zero,neg_add_cancel,ModeCut.cutdet_upper,fromRows_mul_fromCols,
    fromBlocks_add,ModeCut.cutdet_lower,ModeCut.cutdet_id,_root_.mul_one,_root_.one_mul]

theorem cutdet_predicted (hu : Fit R P U) (hm : Fit R Q M) (hf : Fit P P F) (hk : Fit R R K) :
    Touch (fun t => ((P.direct Q).direct R).cutdet (predicted (F t) (U t) (M t) (K t)))
      (fun t => P.cutdet (F t) * R.cutdet (K t) * Q.cutdet ((M t)ᵀ * M t)^2) := by
  simp_rw [← u_y_w_gram]
  have h := (hf.blocks (Fit.zero _ _) (Fit.zero _ _) (Fit.one Q)).blocks (Fit.zero _ _) (Fit.zero _ _) hk
  have hu' := u_y_w_det hu hm
  refine (cutdet_congr (u_y_w_fit hu hm) h).trans ?_
  simp only [ModeCut.cutdet_upper,ModeCut.cutdet_id,_root_.mul_one,pow_two]
  exact ((Touch.refl hf.cutdet_cont).mul (Touch.refl hk.cutdet_cont)).mul (hu'.mul hu')

theorem log_predicted (hu : Fit R P U) (hm : Fit R Q M) (hf : Fit P P F) (hk : Fit R R K)
    (hK : R.cutdet (K 0) ≠ 0) (hG : Q.cutdet ((M 0)ᵀ * M 0) ≠ 0) (hF : P.cutdet (F 0) ≠ 0) :
    Touch (fun t => 1/2 * ((P.direct Q).direct R).cutlog (predicted (F t) (U t) (M t) (K t)) -
        Q.cutlog ((M t)ᵀ * M t))
      (fun t => 1/2 * P.cutlog (F t) + 1/2 * R.cutlog (K t)) := by
  unfold ModeCut.cutlog
  have h := cutdet_predicted hu hm hf hk
  have hg := (hm.tr.mul hm).cutdet_cont
  refine (((Touch.const (1/2:ℝ)).mul (h.log ?_)).sub (Touch.refl (hg.log hG))).congr .rfl ?_
  · exact h.zero.symm ▸ mul_ne_zero (mul_ne_zero hF hK) (pow_ne_zero _ hG)
  filter_upwards [hf.cutdet_cont.eventually_ne hF,hk.cutdet_cont.eventually_ne hK,hg.eventually_ne hG] with t ht hu hv
  rw [Real.log_mul (mul_ne_zero ht hu) (pow_ne_zero 2 hv),Real.log_mul ht hu,Real.log_pow]
  push_cast
  ring

end Det
end ExactRunning

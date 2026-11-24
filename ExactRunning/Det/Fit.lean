import Mathlib.Topology.Instances.Matrix
import ExactRunning.Det.Cut

/-!
# Matrix functions respecting the cut through *first* order

For such (`Fit`) functions compression respects multiplication through
*second* order: off-cut entries (allowed ↔ disallowed couplings) are
little-o of t and products pick them up in pairs. Get the cut determinant
product rule and `det(1+AB)` swap through second order (`Touch`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Matrix Filter
open scoped Topology ContDiff

namespace ExactRunning

variable {m n k j : Type} [Fintype m] [Fintype n] [Fintype k] [Fintype j]
  [DecidableEq m] [DecidableEq n] [DecidableEq k] [DecidableEq j]

open Asymptotics
variable {P : ModeCut m} {Q : ModeCut n} {R : ModeCut k} {S : ModeCut j}


def MatCont (A : ℝ → Matrix m n ℝ) := ∀ a b, ContinuousAt (fun t => A t a b) 0

variable {A A' : ℝ → Matrix m n ℝ} {B B' : ℝ → Matrix n k ℝ}
  {M N : ℝ → Matrix m m ℝ}

namespace MatCont
lemma iff_cont : MatCont A ↔ ContinuousAt A 0 := (continuousAt_pi.trans
    (forall_congr' fun _ => continuousAt_pi)).symm

lemma const (X : Matrix m n ℝ) : MatCont (fun _ => X) := fun _ _ => continuousAt_const

lemma mul (h : MatCont A) (i : MatCont B) : MatCont (fun t => A t * B t) :=
  iff_cont.2 (((continuous_fst : Continuous (Prod.fst :
      Matrix m n ℝ × Matrix n k ℝ → _)).matrix_mul continuous_snd).continuousAt.comp
    ((iff_cont.mp h).prodMk (iff_cont.mp i)))

lemma add (h : MatCont A) (i : MatCont A') : MatCont (fun t => A t + A' t) :=
  fun _ _ => (h _ _).add (i _ _)
lemma sub (h : MatCont A) (i : MatCont A') : MatCont (fun t => A t - A' t) :=
  fun _ _ => (h _ _).sub (i _ _)

lemma det (h : MatCont M) : ContinuousAt (fun t => (M t).det) 0 :=
  continuous_id.matrix_det.continuousAt.comp (iff_cont.mp h)
end MatCont

def Van1 (A : ℝ → Matrix m n ℝ) :=
  ∀ a b, (fun t => A t a b) =o[𝓝 0] fun t => t

structure Fit (P : ModeCut m) (Q : ModeCut n) (A : ℝ → Matrix m n ℝ) : Prop where
  cont : MatCont A
  van : Van1 (fun t => P.e * A t - A t * Q.e)

namespace Van1
lemma mul_left (h : MatCont A) (i : Van1 B) :
    Van1 (fun t => A t * B t) := by
  intro a c
  exact IsLittleO.sum (A:=fun b t => A t a b * B t b c)
    fun b _ => (((h a b).tendsto.isBigO_one ℝ).mul_isLittleO (i b c)).congr_right fun t => by simp

lemma mul_right (h : Van1 A) (i : MatCont B) :
    Van1 (fun t => A t * B t) := by
  intro a c
  exact IsLittleO.sum (A:=fun b t => A t a b * B t b c)
    fun b _ => ((h a b).mul_isBigO ((i b c).tendsto.isBigO_one ℝ)).congr_right fun t => by simp

lemma congr (h : Van1 A) (i : A =ᶠ[𝓝 0] A') : Van1 A' :=
  fun a b => (h a b).congr' (i.mono fun _ ht => congr_fun (congr_fun ht a) b) .rfl
lemma add (h : Van1 A) (i : Van1 A') : Van1 (fun t => A t + A' t) :=
  fun a b => (h a b).add (i a b)
end Van1

namespace Fit
lemma at_zero (h : Fit P Q A) : P.e * A 0 = A 0 * Q.e := by
  ext a b
  have ht := ((h.van a b).def zero_lt_one).self_of_nhds
  simpa [sub_eq_zero] using ht

lemma congr (h : Fit P Q A) (i : A =ᶠ[𝓝 0] A') : Fit P Q A' where
  cont := MatCont.iff_cont.2 ((MatCont.iff_cont.mp h.cont).congr_of_eventuallyEq i.symm)
  van := h.van.congr <| i.mono fun _ ht => congr_arg (fun X => P.e * X - X * Q.e) ht

lemma add (h : Fit P Q A) (i : Fit P Q A') :
    Fit P Q (fun t => A t + A' t) where
  cont := h.cont.add i.cont
  van := (h.van.add i.van).congr (Eventually.of_forall fun _ => by simp only [Matrix.mul_add,Matrix.add_mul]; abel)

lemma neg (h : Fit P Q A) : Fit P Q (fun t => -(A t)) where
  cont := fun _ _ => (h.cont _ _).neg
  van := by
    simp only [Matrix.mul_neg,Matrix.neg_mul, ← neg_sub']
    exact fun _ _ => (h.van _ _).neg_left

lemma sub (h : Fit P Q A) (i : Fit P Q A') :
    Fit P Q (fun t => A t - A' t) := by
  simp_rw [sub_eq_add_neg]
  exact h.add i.neg

lemma mul (h : Fit P Q A) (i : Fit Q R B) : Fit P R (fun t => A t * B t) where
  cont := h.cont.mul i.cont
  van := ((h.van.mul_right i.cont).add (i.van.mul_left h.cont)).congr
    (Eventually.of_forall fun _ => by simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]; abel)

lemma tr (h : Fit P Q A) : Fit Q P (fun t => (A t)ᵀ) where
  cont := fun a b => h.cont b a
  van := by
    have ht : Van1 (fun t => -(P.e * A t - A t * Q.e)ᵀ) := fun a b => (h.van b a).neg_left
    simpa [transpose_mul] using ht

lemma const {X : Matrix m n ℝ} (h : P.e * X = X * Q.e) : Fit P Q (fun _ => X) :=
  ⟨MatCont.const _,by rw [h, sub_self];exact fun a b => isLittleO_zero ..⟩

lemma zero (P : ModeCut m) (Q : ModeCut n) : Fit P Q (fun _ => 0) := const (by simp)
lemma one (P : ModeCut m) : Fit P P (fun _ => 1) := const (by simp)

lemma inv (h : Fit P P M) (hm : (M 0).det ≠ 0) : Fit P P (fun t => (M t)⁻¹) := by
  have hc : MatCont (fun t => (M t)⁻¹) := MatCont.iff_cont.mpr
    ((continuousAt_matrix_inv _ (by rw [show (Ring.inverse : ℝ → ℝ) = Inv.inv from funext Ring.inverse_eq_inv]; exact continuousAt_inv₀ hm)).comp
      (MatCont.iff_cont.mp h.cont))
  refine ⟨hc, ?_⟩
  have hg : Van1 (fun t => -((M t)⁻¹ * (P.e * M t - M t * P.e) * (M t)⁻¹)) :=
    fun _ _ => (((h.van.mul_left hc).mul_right hc) _ _).neg_left
  refine hg.congr ?_
  filter_upwards [h.cont.det.eventually_ne hm] with t ht
  dsimp at ht ⊢
  rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_assoc P.e,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr ht),
      Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc (M t)⁻¹, ← Matrix.mul_assoc (M t)⁻¹ _ P.e,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ht)]
  simp

lemma blocks {B : ℝ → Matrix m j ℝ} {C : ℝ → Matrix k n ℝ} {D : ℝ → Matrix k j ℝ}
    (ha : Fit P Q A) (hb : Fit P S B) (hc : Fit R Q C) (hd : Fit R S D) :
    Fit (P.direct R) (Q.direct S) (fun t => fromBlocks (A t) (B t) (C t) (D t)) where
  cont
    | .inl a,.inl b => ha.cont a b
    | .inl a,.inr b => hb.cont a b
    | .inr a,.inl b => hc.cont a b
    | .inr a,.inr b => hd.cont a b
  van := by
    simp only [ModeCut.direct_e, fromBlocks_multiply,Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add]
    rintro (a|a) (b|b)
    · exact ha.van a b
    · exact hb.van a b
    · exact hc.van a b
    · exact hd.van a b

/-- Entrywise derivative along a ray. -/
def diff (A : ℝ → Matrix m n ℝ) : Matrix m n ℝ :=
  of fun a b => deriv (fun t => A t a b) 0

lemma of_deriv (h : ∀ a b, DifferentiableAt ℝ (fun t => A t a b) 0)
    (hi : P.e * A 0 = A 0 * Q.e)
    (hk : P.e * diff A = diff A * Q.e) : Fit P Q A where
  cont := fun a b => (h a b).continuousAt
  van := by
    intro a b
    have h1 : HasDerivAt (fun t => (P.e * A t) a b) ((P.e * diff A) a b) 0 :=
      by simp only [Matrix.mul_apply,diff,of_apply]; exact HasDerivAt.fun_sum fun d _ => (h d b).hasDerivAt.const_mul _
    have h2 : HasDerivAt (fun t => (A t * Q.e) a b) ((diff A * Q.e) a b) 0 :=
      by simp only [Matrix.mul_apply,diff,of_apply]; exact HasDerivAt.fun_sum fun d _ => (h a d).hasDerivAt.mul_const _
    simpa [hi,hk] using (hasDerivAt_iff_isLittleO_nhds_zero.mp (h1.sub h2))
end Fit

def MatTouch (A B : ℝ → Matrix m n ℝ) :=
  ∀ a b, Touch (fun t => A t a b) (fun t => B t a b)
namespace MatTouch

lemma refl (h : MatCont A) : MatTouch A A := fun a b => Touch.refl (h a b)
lemma const (X : Matrix m n ℝ) : MatTouch (fun _ => X) (fun _ => X) :=
  refl (MatCont.const X)
lemma mul (h : MatTouch A A') (i : MatTouch B B') :
    MatTouch (fun t => A t * B t) (fun t => A' t * B' t) := by
  intro a b; simp only [Matrix.mul_apply]
  exact Touch.sum fun c _ => (h a c).mul (i c b)
lemma add {B B' : ℝ → Matrix m n ℝ} (h : MatTouch A A') (i : MatTouch B B') :
    MatTouch (fun t => A t + B t) (fun t => A' t + B' t) :=
  fun a b => (h a b).add (i a b)
lemma det (h : MatTouch M N) :
    Touch (fun t => (M t).det) (fun t => (N t).det) := by
  simp only [Matrix.det_apply,Units.smul_def,zsmul_eq_mul]
  exact Touch.sum fun _ _ => (Touch.const _).mul (Touch.prod fun _ _ => h _ _)

lemma cutdet (h : MatTouch M N) (P : ModeCut m) :
    Touch (fun t => P.cutdet (M t)) (fun t => P.cutdet (N t)) :=
  ((((const P.e).mul h).mul (const P.e)).add (const (1-P.e))).det

lemma of_van (h : Van1 A) (i : Van1 B)
    {U V : ℝ → Matrix m k ℝ} (hu : MatCont U) (hv : MatCont V)
    (he : ∀ t,U t - V t = A t * B t) :
    MatTouch U V := by
  intro a b
  refine ⟨hu a b,hv a b,?_⟩
  simp_rw [← Matrix.sub_apply,he, Matrix.mul_apply]
  exact IsLittleO.sum fun c _ => ((h a c).mul (i c b)).congr_right fun _ => (sq _).symm

end MatTouch

namespace Fit
lemma off_left (h : Fit P Q A) :
    Van1 (fun t => P.e * A t * (1-Q.e)) :=
  (h.van.mul_right (MatCont.const (1-Q.e))).congr <|
    Eventually.of_forall fun _ => by dsimp;rw [Matrix.sub_mul, Matrix.mul_assoc _ Q.e, Q.elim, Matrix.mul_zero, sub_zero]

lemma off_right (h : Fit P Q A) :
    Van1 (fun t => (1-P.e) * A t * Q.e) := by
  have ht := h.tr.off_left
  have hc : Van1 (fun t => (Q.e * (A t)ᵀ * (1-P.e))ᵀ) := fun _ _ => ht _ _
  simpa [Matrix.mul_assoc] using hc

lemma project_mul (h : Fit P Q A) (i : Fit Q R B) :
    MatTouch (fun t => P.e * (A t * B t) * R.e)
       (fun t => (P.e * A t * Q.e) * (Q.e * B t * R.e)) :=
    MatTouch.of_van h.off_left i.off_right
      (((MatCont.const _).mul (h.cont.mul i.cont)).mul (MatCont.const _))
      ((((MatCont.const _).mul h.cont).mul (MatCont.const _)).mul
        (((MatCont.const _).mul i.cont).mul (MatCont.const _)))
      fun _ => P.proj_mul_aux Q R _ _

/-- Multiplicativity through order two. -/
lemma cutdet_mul (h : Fit P P M) (i : Fit P P N) :
    Touch (fun t => P.cutdet (M t * N t))
          (fun t => P.cutdet (M t) * P.cutdet (N t)) := by
  exact (((h.project_mul i).add (MatTouch.const (1-P.e))).det).congr .rfl
    (Eventually.of_forall fun _ => by dsimp [ModeCut.cutdet];rw [← Matrix.det_mul,P.compMat_mul_aux])

lemma cutdet_sylvester {B : ℝ → Matrix n m ℝ} (h : Fit P Q A) (i : Fit Q P B) :
    Touch (fun t => P.cutdet (1 + A t * B t))
          (fun t => Q.cutdet (1 + B t * A t)) := by
  simp only [ModeCut.cutdet, ModeCut.compMat_one_add]
  refine ((MatTouch.const 1).add (h.project_mul i)).det.trans ?_
  simp_rw [Matrix.det_one_add_mul_comm (P.e * (_ : Matrix m n ℝ) * Q.e) (Q.e * (_ : Matrix n m ℝ) * P.e)]
  exact ((MatTouch.const 1).add (i.project_mul h)).det.symm

end Fit
end ExactRunning

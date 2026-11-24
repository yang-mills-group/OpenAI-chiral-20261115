import YM.Laurent.Art
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern
open YM YM.Laurent

open Lattice

/-! Scalars with summable moments, positive-exponent convention:
displacement x indexes the column minus the row. -/

abbrev Brill := Rim Axis

def pen (k : ℕ) (x : Cover) : ℝ := (1+(size x:ℝ))^k

@[simp] lemma pen_zero (x : Cover) : pen 0 x = 1 := by simp [pen]
lemma penPos (k : ℕ) (x : Cover) : 0 < pen k x := by unfold pen; positivity

lemma penAdd (k : ℕ) (a b : Cover) : pen k (a+b) ≤ pen k a * pen k b := by
  unfold pen; rw [← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ _
  have h : (size (a+b) : ℝ) ≤ size a+size b := by exact_mod_cast size_add a b
  nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) (size a)) (Nat.cast_nonneg (size b))]

def Fast (f : Cover → ℂ) := ∀ k, Summable (fun x => pen k x * ‖f x‖)

variable {f g : Cover → ℂ}
def pile (f g : Cover → ℂ) : Cover → ℂ :=
  fun x => ∑' y, f y * g (x-y)

lemma Fast.abs (h : Fast f) : Summable (fun x => ‖f x‖) := by
  simpa only [pen_zero, one_mul] using h 0

lemma Fast.sum (h : Fast f) : Summable f := h.abs.of_norm

lemma Fast.add (hf : Fast f) (hg : Fast g) : Fast (f+g) := fun k =>
  ((hf k).add (hg k)).of_nonneg_of_le
    (fun x => mul_nonneg (penPos ..).le (norm_nonneg _)) (fun x => by
      rw [Pi.add_apply, ←mul_add]
      exact mul_le_mul_of_nonneg_left (norm_add_le ..) (penPos ..).le)

lemma Fast.neg (hf : Fast f) : Fast (-f) := fun k => by simpa only [Pi.neg_apply,norm_neg] using hf k

def splitLeft : Cover × Cover ≃ Cover × Cover where
  toFun q := (q.2,q.1-q.2)
  invFun p := (p.2+p.1,p.1)
  left_inv _ := Prod.ext (sub_add_cancel ..) rfl
  right_inv _ := Prod.ext rfl (add_sub_cancel_right ..)

lemma Fast.splitAbsW (hf : Fast f) (hg : Fast g) (k) :
    Summable (fun q : Cover×Cover => pen k q.1 * ‖f q.2 * g (q.1-q.2)‖) := by
  have h := (hf k).mul_of_nonneg (hg k)
    (fun x => mul_nonneg (penPos ..).le (norm_nonneg _)) (fun x => mul_nonneg (penPos ..).le (norm_nonneg _))
  apply (splitLeft.summable_iff.mpr h).of_nonneg_of_le
  · intro; exact mul_nonneg (penPos ..).le (norm_nonneg _)
  rintro ⟨x,y⟩
  change pen k x * ‖_ * _‖ ≤ (pen k y * ‖f y‖) * (pen k (x-y) * ‖g (x-y)‖)
  have hh := penAdd k y (x-y)

  rw [norm_mul, mul_mul_mul_comm]
  rw [add_comm, sub_add_cancel] at hh
  exact mul_le_mul_of_nonneg_right hh (by positivity)

lemma Fast.splitAbs (hf : Fast f) (hg : Fast g) :
    Summable (fun q : Cover×Cover => ‖f q.2 * g (q.1-q.2)‖) := by
  simpa only [pen_zero,one_mul] using hf.splitAbsW hg 0

lemma Fast.pack (hf : Fast f) (hg : Fast g) (x : Cover) :
    Summable (fun y => f y * g (x-y)) :=
  ((hf.splitAbs hg).prod_factor x).of_norm

lemma Fast.pile (hf : Fast f) (hg : Fast g) : Fast (pile f g) := by
  intro k
  apply (hf.splitAbsW hg k).prod.of_nonneg_of_le
  · intro; exact mul_nonneg (penPos ..).le (norm_nonneg _)
  intro x
  dsimp only
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm ((hf.splitAbs hg).prod_factor x)) (penPos ..).le

open UnitAddTorus

def vista (f : Cover → ℂ) (t : Brill) : ℂ :=
  ∑' x, mFourier x t * f x

lemma badge (x : Cover) (t : Brill) : ‖mFourier x t‖=1 := by
  simp [mFourier, fourier_apply]

lemma Fast.shown (hf : Fast f) (t : Brill) : Fast (fun x => mFourier x t * f x) := by
  intro k
  simpa only [norm_mul,badge,one_mul] using hf k


lemma vista_add (hf : Fast f) (hg : Fast g) :
    vista (f+g) = vista f+vista g := by
  funext t
  rw [Pi.add_apply,vista,vista,vista, ←(hf.shown t).sum.tsum_add (hg.shown t).sum]
  simp_rw [Pi.add_apply, mul_add]

lemma vista_neg (f : Cover → ℂ) : vista (-f) = - vista f :=
  funext (fun t => by simp only [Pi.neg_apply,vista,mul_neg,tsum_neg])

lemma vista_prod (hf : Fast f) (hg : Fast g) :
    vista (pile f g) = vista f * vista g := by
  funext t
  let u := fun x => mFourier x t * f x
  let v := fun x => mFourier x t * g x
  change _ = (∑' x, u x) * ∑' y, v y
  have h := ((hf.shown t).splitAbs (hg.shown t)).of_norm
  rw [tsum_mul_tsum_of_summable_norm (hf.shown t).abs (hg.shown t).abs, ←splitLeft.tsum_eq]
  refine Eq.trans ?_ h.tsum_prod.symm
  unfold vista pile
  simp_rw [←tsum_mul_left]
  refine tsum_congr fun x => tsum_congr fun y => ?_
  change mFourier x t * (f y * g (x-y)) = u y * v (x-y)
  dsimp [u,v]
  rw [mul_mul_mul_comm, ←mFourier_add, add_comm y, sub_add_cancel]

def echo (c : ℂ) (x : Cover) : ℂ := if x=0 then c else 0

lemma fast_echo (c : ℂ) : Fast (echo c) := by
  intro k
  suffices h : (fun x => pen k x * ‖echo c x‖) = fun x => if x=0 then pen k 0 * ‖c‖ else 0 by
    rw [h]; exact (hasSum_ite_eq (0:Cover) _).summable
  funext x; by_cases hx : x=0 <;> simp [echo,hx]

lemma vista_echo (c : ℂ) (t : Brill) : vista (echo c) t=c := by
  rw [vista,tsum_eq_single 0]
  · simp [mFourier_zero,echo]
  intro b hb; simp [echo,hb]

open MeasureTheory

lemma inner_badge (x y : Cover) :
    (∫ t, mFourier y t * mFourier (-x) t ∂globe Axis) = if x=y then 1 else 0 := by
  have e := orthonormal_iff_ite.mp orthonormal_mFourier x y
  simp only [mFourier_neg]
  simpa only [mFourierLp, ContinuousMap.inner_toLp] using! e

lemma vista_cont (hf : Fast f) : Continuous (vista f) :=
  continuous_tsum (u:=fun x => ‖f x‖)
    (fun x => (mFourier x).continuous.mul continuous_const)
    hf.abs (fun x t => le_of_eq (by rw [norm_mul,badge,one_mul]))


lemma recover (hf : Fast f) (x : Cover) :
    (∫ t, vista f t * mFourier (-x) t ∂globe Axis) = f x := by
  let B := fun (y : Cover) (t : Brill) => (mFourier y t * mFourier (-x) t) * f y
  have bh (y : Cover) (t : Brill) : ‖B y t‖ = ‖f y‖ := by
    simp only [B,norm_mul,badge,one_mul]
  have bo (y : Cover) : Integrable (B y) (globe Axis) :=
    Integrable.mono' (integrable_const ‖f y‖)
      (((mFourier y).continuous.mul (mFourier (-x)).continuous).mul
        (continuous_const (y:=f y))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => (bh y t).le)
  have bs : Summable (fun y => ∫ t, ‖B y t‖ ∂globe Axis) := by
    simpa [bh] using hf.abs
  have e (t) : vista f t * mFourier (-x) t = ∑' y, B y t := by
    rw [vista, ←tsum_mul_right]; simp only [mul_right_comm _ _ (mFourier (-x) t),B]
  simp_rw [e]
  rw [←integral_tsum_of_summable_integral_norm bo bs]

  rw [tsum_eq_single x]
  · simp [B,integral_mul_const,inner_badge]
  intro b h; simp [B,integral_mul_const,inner_badge,h.symm]

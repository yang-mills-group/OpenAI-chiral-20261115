import Mathlib.Analysis.Calculus.SmoothSeries
import YM.CF.Fir.Cue
import Zephyr.Chern.Grad
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice UnitAddTorus Silk YM.Laurent YM.CF YM.CF.Fir YM.Next.Free


open scoped Real  -- π

def radians (p : Axis → ℝ) : Brill :=
  dress Axis fun i=>p i/(2*π)

@[simp] lemma rad_zero : radians 0 = 0 := by
  funext i
  change (((0:ℝ)/(2*π):ℝ) : UnitAddCircle) = 0
  simp

lemma rad_forward (p) (x : Cover) : mFourier x (radians p) = mode (tmap p) x := by
  rw [radians, wears]
  congr
  funext i
  change 2*(π:ℂ)*(((p i/(2*π):ℝ)):ℂ)=(p i:ℂ)
  push_cast
  rw [mul_div_cancel₀ _ (show (2:ℂ)*(π:ℝ)≠0 from mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'))]

lemma rad_cover (t : Brill) :
    ∃ p, radians p = t ∧ ∀ i, |p i| ≤ π := by
  let b := AddCircle.equivIoc (1:ℝ) (-1/2)
  let p (i:Axis):= (b (t i)).val
  refine ⟨fun i=> p i * (2*π),?_,fun i=>?_⟩
  · unfold radians
    simp_rw [mul_div_cancel_right₀ _ (by positivity : 2*π≠0)]
    exact funext fun i=> AddCircle.coe_equivIoc

  · have hp := (b (t i)).prop
    have a : -1/2 < p i := hp.1
    have c : p i ≤ -1/2+1 := hp.2
    rw [abs_le]
    constructor <;> nlinarith [Real.pi_pos, mul_nonneg (by linarith : 0 ≤ 1/2 - p i) Real.pi_pos.le,
      mul_nonneg (by linarith : 0 ≤ p i + 1/2) Real.pi_pos.le]

lemma rad_cube {p : Axis → ℝ} (h : ∀ i:Axis,|p i|≤π) : tmap p ∈ baseCube :=
  ⟨tmap_physical _,fun i=> h i⟩

lemma E_read (f : Silk) (p) :
    E (radians p) f = YM.Laurent.read f.co (tmap p) := by
  rw [E_eq,vista,YM.Laurent.read]
  simp only [rad_forward, smul_eq_mul]

private lemma factor_eq (j : Axis) (x : Cover) (t : ℝ) :
    mFourier x (radians (Pi.single j t))=Complex.exp (t*rune j x) := by
  rw [rad_forward,mode, Finset.sum_eq_single j]
  · rw [tmap,Pi.single_eq_same,rune]; ring_nf
  · intro i _ h;rw [tmap,Pi.single_eq_of_ne h, Complex.ofReal_zero,zero_mul]
  simp

private lemma factor (j : Axis) (x : Cover) (t : ℝ) :
    HasDerivAt (fun r : ℝ => mFourier x (radians (Pi.single j r)))
      (mFourier x (radians (Pi.single j t))*rune j x) t := by
  simp_rw [factor_eq]
  simpa only [Complex.ofReal_one,one_mul] using
    (((hasDerivAt_id' t).ofReal_comp).mul_const (rune j x)).cexp

lemma E_along (j : Axis) (f : Silk) (t : ℝ) :
    HasDerivAt (fun r:ℝ => E (radians (Pi.single j r)) f)
      (E (radians (Pi.single j t)) (D j f)) t := by
  let m x r := mFourier x (radians (Pi.single j r))
  have hd (x : Cover) (r : ℝ) :
      HasDerivAt (fun s => m x s * f.co x) (m x r * (D j f).co x) r := by
    rw [co_D,←mul_assoc]; exact (factor j x r).mul_const _
  exact hasDerivAt_tsum (D j f).fast.abs hd
    (fun x r => by change ‖mFourier x _* _‖ ≤ _;rw [norm_mul,badge,one_mul])
    (f.fast.shown (radians (Pi.single j t))).sum t

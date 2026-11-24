import Zephyr.Chern.Limits
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice Filter YM.Laurent


lemma poly (a : ℝ) (k : ℕ) (ha : 0<a) :
    ∃ L:ℝ,0<L ∧ ∀ t:ℝ,0≤t → (1+t)^k ≤ L*Real.exp (a*t) := by
  cases k with
  | zero => exact ⟨1,zero_lt_one,fun t h => by rw [pow_zero,one_mul];exact Real.one_le_exp (by positivity)⟩
  | succ n =>
    let b:=a/(n.succ:ℝ)
    have hb : 0<b:=by unfold b;positivity
    use (1+1/b)^n.succ, by positivity
    intro t h
    have e : 1+t ≤ (1+1/b)*Real.exp (b*t) := by
      apply le_trans _ (mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (by positivity : 0≤1+1/b))
      rw [add_mul, mul_add (1/b),←mul_assoc (1/b), one_div,inv_mul_cancel₀ hb.ne']
      nlinarith [inv_pos.mpr hb]
    have ht: a*t=n.succ*(b*t) := by rw [←mul_assoc]; unfold b;field_simp
    rw [ht,Real.exp_nat_mul,←mul_pow]
    exact pow_le_pow_left₀ (by positivity) e _

lemma fast_kernel {b : ℝ} (C : ℝ) (h : 0<b) :
    Fast (fun x => ((C*Real.exp (-b*size x):ℝ):ℂ)) := by
  intro k
  let a:= b/2
  have ha : 0<a:= half_pos h
  obtain ⟨D,hD,H⟩:=poly a k ha

  apply ((Width.compactPay (α:=Axis) a ha).2.1.mul_left (D*|C|)).of_nonneg_of_le
  · intro;exact mul_nonneg (penPos ..).le (norm_nonneg _)
  intro x
  rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  apply le_trans (mul_le_mul_of_nonneg_right (H _ (Nat.cast_nonneg (size x))) (by positivity))
  have e: -(a)*(size x:ℝ) = a*size x + -b*size x := by unfold a;ring
  rw [e,Real.exp_add]; exact le_of_eq (by ring)

lemma swift_exp {I : Type*} {F : Filter I} {f : I → Cover → ℂ}
    {a : ℝ} (ha : 0<a) (C : ℝ)
    (h : ∀ᶠ i in F, ∀ x,‖f i x‖ ≤ C*Real.exp (-a*size x)) : Swift F f :=
  ⟨_,fast_kernel C ha, h.mono fun i p x => le_trans (p x) (by
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact le_abs_self _)⟩

lemma of_width {f : Cover → ℂ} {a C : ℝ} (h : Width a C f) (x) :
    ‖f x‖ ≤ C*Real.exp (-a*size x) := by
  rw [neg_mul,Real.exp_neg, ← div_eq_mul_inv]
  exact (le_div_iff₀' (Real.exp_pos _)).mpr ((h.2.1.le_tsum x (fun y _=>h.1 y)).trans h.2.2)

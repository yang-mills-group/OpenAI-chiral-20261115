import YM.CF.Vp929.Analysis.Slit

noncomputable section
set_option autoImplicit false
namespace YM.CF.VolumeRate
open Set Metric Filter

/-- The uniform rate barrier, one hop up the slit ladder (move to L times larger side).
Picking A as a strict supersolution avoids choosing maxima hop-by-hop. Here v stands for volume,
s for `L^4`.
-/
lemma hop (v s M E A : ℝ) (hv : 0 < v)
    (hp : -A ≤ M) (ht : propagation*(M+A) > M+E + A / s)
    (f g : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball 0 1))
    (hu : ∀ z ∈ ball (0:ℂ) 1, ‖f z‖ ≤ Real.exp (M*v))
    (hl : ∃ x : ℝ, |x| ≤ 1/8 ∧ Real.exp (-A*(v/s)) ≤ ‖g x‖)
    (h : ∀ x : ℝ, |x| ≤ 1/8 → ∃ y : ℝ, |y| ≤ 1/4 ∧ Real.exp (-E*v) * ‖g x‖ ≤ ‖f y‖) :
    ∃ y : ℝ, |y| ≤ 1/8 ∧ Real.exp (-A*v) ≤ ‖f y‖ := by
  by_contra! HH; obtain ⟨x,hx,p⟩:=hl; obtain ⟨y,hy,q⟩:= h x hx
  have H:= (mul_le_mul_of_nonneg_left p (Real.exp_pos (-E*v)).le).trans <|
    q.trans (slit_propagation (mul_le_mul_of_nonneg_right hp hv.le) hf hu (fun z hz=>(HH z hz).le) y hy)
  rw [← Real.exp_add, Real.exp_le_exp] at H; simp only [div_eq_mul_inv] at *
  linarith [show (M+E+A*s⁻¹)*v < propagation*(M+A)*v from mul_lt_mul_of_pos_right ht hv]

lemma barrier {d s : ℝ} (h : 0 < d) (p : 0 < s) (q : s⁻¹ < propagation) (M E : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ -A ≤ M ∧ propagation*(M+A) > M+E + A / s ∧ Real.exp (-A) ≤ d := by
  obtain ⟨A,h₀,h₁,h₂,h₃⟩:= ((eventually_ge_atTop (0:ℝ)).and ((eventually_ge_atTop (-M)).and
    ((eventually_ge_atTop (-Real.log d)).and (eventually_gt_atTop ((M + E - propagation*M)/(propagation-s⁻¹)))))).exists
  refine ⟨A,h₀,by linarith,?_,(Real.exp_monotone (by linarith : -A ≤ Real.log d)).trans_eq (Real.exp_log h)⟩
  rw [div_eq_mul_inv A]; nlinarith [(div_lt_iff₀ (sub_pos.mpr q)).1 h₃]
end YM.CF.VolumeRate

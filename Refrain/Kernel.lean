import YM.SectorNext.VACUUM_NORMALIZATION.Laplace

/-! # Quantitative scalar one-bond chart (for the real finite-denominator price) -/
set_option autoImplicit false
set_option linter.flexible false
noncomputable section
namespace YM.SectorNext.Vacuum
open Filter Function Set Lattice RG Wilson Pressure Precision MeasureTheory
open scoped Matrix.Norms.Frobenius BigOperators ENNReal Topology ContDiff Classical
open Metric
variable {G:Gauge}
lemma Jacob_linear (A: ChartRatio G)(H:LocalRatio A){r:ℝ}(p:r<A.radius)(u:0≤r):∃ C> (0:ℝ),∀ x:G.Color, ‖x‖ ≤ r → |A.J x-1| ≤ C*‖x‖:=by
 have hf: ContDiffOn ℝ ω A.J (closedBall 0 r):=fun x hx=> (H.germ x (closedBall_subset_ball p hx)).contDiffWithinAt
 obtain ⟨C,hC⟩:= hf.exists_lipschitzOnWith (by simp) (convex_closedBall 0 r) (ProperSpace.isCompact_closedBall ..)
 refine ⟨(C:ℝ)+1,by have he:=C.2; positivity,fun x h=>?_⟩
 have h':=hC.dist_le_mul (x:=x) (by rwa [mem_closedBall,dist_zero_right]) (y:=0) (mem_closedBall_self u)
 rw [H.anchored,Real.dist_eq,dist_zero_right] at h'; exact h'.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg _))

lemma exp_abs_lane (a b:ℝ) : |Real.exp a - Real.exp b| ≤ (Real.exp a+Real.exp b)*|a-b|:=by
 have hp (a b:ℝ)(h:a≤b): Real.exp b-Real.exp a ≤ Real.exp b*(b-a):=by
    have he:= mul_le_mul_of_nonneg_left (Real.add_one_le_exp (a-b)) (Real.exp_pos b).le
    rw [←Real.exp_add,add_sub_cancel b a] at he; linarith
 rcases le_total a b with h|h
 · rw [abs_of_nonpos (sub_nonpos.mpr h),abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr h))]; nlinarith only [hp a b h,mul_nonneg (Real.exp_pos a).le (sub_nonneg.mpr h)]
 rw [abs_of_nonneg (sub_nonneg.mpr h),abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h))]; nlinarith only [hp b a h,mul_nonneg (Real.exp_pos b).le (sub_nonneg.mpr h)]

-- absorbing polynomial powers in Gaussian
lemma poly_lane (n:ℕ){b:ℝ}(hb:0<b):∃ D> (0:ℝ),∀ x≥ (0:ℝ), x^n * Real.exp (-b*x^2) ≤ D*Real.exp (-(b/2)*x^2):=by
 let a:= b/(2*(n+1))
 have he: 0 < a:=by unfold a; positivity
 let u:=a⁻¹+1
 have hu: 0<u:=by unfold u; positivity
 refine ⟨u^n,pow_pos hu _,fun x hx=>?_⟩
 have hp:x≤ u*Real.exp (a*x^2):=by
    apply le_trans _ (mul_le_mul_of_nonneg_left (Real.add_one_le_exp (a*x^2)) hu.le)
    have hi:=inv_pos.mpr he; unfold u; have h0:= inv_mul_cancel₀ he.ne'; nlinarith only [h0,hi, mul_nonneg he.le (sq_nonneg x), sq_nonneg (x-1)] -- h0 * x²? nlinarith only
 have hm:=pow_le_pow_left₀ hx hp n
 rw [mul_pow,← Real.exp_nat_mul] at hm
 calc
    _ ≤ u^n*Real.exp (↑n*(a*x^2))*Real.exp (-b*x^2):=mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
    _ ≤ _:=by rw [mul_assoc,← Real.exp_add]; apply mul_le_mul_of_nonneg_left (Real.exp_monotone _) (pow_nonneg hu.le _); have ha:a*((n:ℝ)+1)=b/2:=by unfold a; field_simp; all_goals ring; -- tune
              nlinarith only [show 0≤a*x^2 from mul_nonneg he.le (sq_nonneg _),congrArg (fun y:ℝ=> y*x^2) ha]

abbrev frost (a:ℝ)(x:G.Color):ℝ:= Real.exp (-a*‖x‖^2)
lemma tint_frost {a:ℝ}(h:0<a): Integrable (frost (G:=G) a):=by
 have hg:= (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (b:=(a:ℂ)) (show 0<a from h) 0 (0:G.Color)).norm
 change Integrable (fun x:G.Color=> Real.exp (-a*‖x‖^2))
 simpa [frost,Complex.norm_exp,pow_two,Complex.mul_re] using hg
lemma tint_grow (n:ℕ){a:ℝ}(h:0<a): Integrable (fun x:G.Color=> ‖x‖^n*frost a x):=by
 obtain ⟨D,hp,hD⟩:=poly_lane n h
 apply ((tint_frost (G:=G) (half_pos h)).const_mul D).mono (show Continuous (fun x:G.Color=> ‖x‖^n*frost a x) by unfold frost; fun_prop).aestronglyMeasurable
 filter_upwards with x; change ‖(_*_ :ℝ)‖ ≤ ‖D*_‖; rw [Real.norm_of_nonneg (show 0≤‖x‖^n*frost a x from mul_nonneg (pow_nonneg (norm_nonneg x) _) (Real.exp_pos _).le),Real.norm_of_nonneg (mul_pos hp (Real.exp_pos _)).le]; exact hD _ (norm_nonneg _)
end YM.SectorNext.Vacuum

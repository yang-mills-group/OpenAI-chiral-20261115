import YM.SU5.Reconstruction.Sleet.Mist
/-! # Moving hol purchase. Need uniform on the infinite tubes. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConePrice.Storm
open Set Filter MeasureTheory Measure Complex Sail YM.Paley Metric
open scoped Topology NNReal Real Classical
variable {F:ℝ→ℂ→ℂ}{G:ℂ→ℝ→ℂ}{d C:ℝ}(κ:Gust d C F G)
private lemma pearl_melt (z:ℂ)(x b:ℝ)(h:‖z‖≤ b): ‖pearl ((x:ℂ)-z)‖≤ Real.exp (2*b^2)/√(Real.pi) * Real.exp (- (1/2:ℝ)*x^2):=by
 rw [pearl_ignition, glimmer, div_mul_eq_mul_div,div_mul_eq_mul_div, ← Real.exp_add,← Real.exp_add]
 gcongr Real.exp ?_ / _ -- tune
 simp only [sub_re,sub_im,ofReal_re,ofReal_im]; have ht:= (abs_re_le_norm z).trans h; have hm:= (abs_im_le_norm z).trans h; have hx : 0 ≤ b:= (norm_nonneg _).trans h
 apply le_trans (show -(x-z.re)^2+(0-z.im)^2 ≤ 2*b^2-1/2*x^2 by nlinarith [sq_nonneg (x/2-z.re), (mul_self_le_mul_self (abs_nonneg _) ht), (mul_self_le_mul_self (abs_nonneg _) hm), abs_mul_abs_self z.re, abs_mul_abs_self z.im])
 linarith
include κ
lemma crystal_turn {W:Set ℂ}(m:ℝ){f g:ℂ→ℂ}(h:IsOpen W)(s:MapsTo g W (slit d))(x:AnalyticOnNhd ℂ f W)(y:AnalyticOnNhd ℂ g W): AnalyticOnNhd ℂ (fun z=>crystal F m (f z) (g z)) W:=by
 apply DifferentiableOn.analyticOnNhd _ h; intro z Z
 let b:= ‖(m:ℂ)*f z‖+1
 let M(u:ℝ):= C*(Real.exp (2*b^2)/√(Real.pi)) * Real.exp (- (1/2:ℝ)*u^2)
 have C₀:0 ≤ C:= (norm_nonneg _).trans (κ.rent 0 (g z) (s Z))
 obtain ⟨r,R,hR⟩:= Metric.mem_nhds_iff.mp (show {i|i∈W∧‖(m:ℂ)*f i‖<b}∈𝓝 z from (Eventually.and (show ∀ᶠ i in 𝓝 z, i∈W from h.mem_nhds Z)
    ((((x z Z).continuousAt.const_mul (m:ℂ)).norm.tendsto).eventually (gt_mem_nhds (show _<b by unfold b; linarith))))) -- tune ≥ vs < order gt_mem
 have hw(i)(p:i∈ball z r): i∈W:= (hR p).1
 refine (averaging_hol (fun i u=> pearl ((u:ℝ) - (m:ℂ)* f i)* F (u/m) (g i)) isOpen_ball (mem_ball_self R)
    ((integrable_exp_neg_mul_sq (b:= (1/2:ℝ)) (by norm_num)).const_mul (C*(Real.exp (2*b^2)/√(Real.pi)))) ?_ ?_ ?_).differentiableWithinAt
 · intro i t; apply Continuous.aestronglyMeasurable; unfold pearl; refine Continuous.mul (by fun_prop) ((κ.comes (g i) (s (hw i t))).comp (f:=fun u:ℝ=> u/m) (by fun_prop))
 · intro i t k; rw [norm_mul]; refine (mul_le_mul (pearl_melt _ _ b ((show ‖_‖<b from (hR t).2).le)) (κ.rent _ _ (s (hw i t))) (norm_nonneg _) (by positivity)).trans_eq ?_; ring
 intro i; apply AnalyticOnNhd.differentiableOn; intro j p; refine AnalyticAt.mul ?_ ((κ.usable (i/m) (g j) (s (hw j p))).comp (y j (hw j p)))
 unfold pearl; have ht:= x j (hw j p); fun_prop (disch:=positivity)

lemma ported_turn (m:ℝ)(v:ℝ): AnalyticOnNhd ℂ (fun z=>ported G m z v) (slit d):=by
 have hw(x z)(p:z∈slit d): (↑(x/m):ℂ)+z∈ slit d:=by change |_|<d; simpa using (show |z.im|<d from p)
 apply DifferentiableOn.analyticOnNhd _ (slit_open d); intro z p
 apply (averaging_hol (fun z (t:ℝ)=> (glimmer t:ℂ) * G ((↑(t/m):ℂ)+z) v) (slit_open d) p (glimmer_ok.mul_const C) ?_ ?_ ?_).differentiableWithinAt
 · intro y h; refine (Continuous.mul ?_ ((κ.guides v).continuousOn.comp_continuous ?_ (fun x=> hw x y h))).aestronglyMeasurable <;> first | unfold glimmer;fun_prop | fun_prop
 · intro y h i; rw [norm_mul, Complex.norm_real,Real.norm_of_nonneg (glimmer_pos _)]; apply mul_le_mul_of_nonneg_left (κ.charge _ _ (hw i _ h)) (glimmer_pos _)
 intro i; apply AnalyticOnNhd.differentiableOn; intro y h; refine analyticAt_const.mul ((κ.guides v _ (hw i _ h)).comp (analyticAt_const.add analyticAt_id))
lemma ported_crown(m:ℝ)(h:m≠0)(z:ℂ)(e:z∈slit d)(v:ℝ):crystal F m z v=ported G m z v:= by
 refine pioneer (slit_connected d) (slit_ground d κ.pos 0) (-1) 1 (by norm_num)
    (M₁:=fun z:ℂ=>crystal F m z v) (crystal_turn κ m (slit_open d) (fun _ _=> slit_ground d κ.pos v) (fun z _=> analyticAt_id) analyticOnNhd_const) (ported_turn κ m v) (fun x _=>ported_real κ m h x v) e
end YM.ConePrice.Storm

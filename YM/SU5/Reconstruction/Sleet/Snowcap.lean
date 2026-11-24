import YM.SU5.Reconstruction.Sleet.Cloudbase
/-! # Analytical power bill from stamp samples. No operator radius budget. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConePrice.Storm
open Set Filter MeasureTheory Complex Sail Metric CF.Floral
open scoped Topology NNReal Real Classical
open scoped BoundedContinuousFunction

local notation "Pe"=> ℝ≥0 →ᵇ ℂ
private def coast (n:ℕ):Pe:=BoundedContinuousFunction.ofNormedAddCommGroup (fun x=> ((min (x:ℝ) n:ℝ):ℂ)) (by fun_prop) n (fun x=>by
 rw [norm_real,Real.norm_of_nonneg (by exact le_min (by positivity) (by positivity))]; exact min_le_right _ _)
private def mantled(n:ℕ)(z:ℂ):Pe:=NormedSpace.exp ((-z) • coast n)
private def clipExp(z:ℂ)(x:ℝ):=Complex.exp (-z*(x:ℂ))
private lemma mantled_hit(n:ℕ)(z:ℂ)(x:ℝ≥0): mantled n z x = clipExp z (min (x:ℝ) n):=by
 let K: Pe →+* ℂ:= { toFun f:=f x, map_one':=rfl,map_zero':=rfl,map_add' f g:=rfl,map_mul' f g:=rfl }
 letI : NormedAlgebra ℚ Pe:=NormedAlgebra.restrictScalars ℚ ℂ _ -- or inferred
 unfold clipExp; rw [Complex.exp_eq_exp_ℂ]; exact NormedSpace.map_exp K (BoundedContinuousFunction.evalCLM ℂ x).cont ((-z) • coast n)
private lemma clip_size (z:ℂ)(x:ℝ): ‖clipExp z x‖ = Real.exp (-z.re*x):=by unfold clipExp; simp [norm_exp,mul_re]
private lemma most_hand (z:ℂ)(p:z∈optimistic)(x:ℝ)(u:0≤x): ‖clipExp z x‖≤1:=by rw [clip_size,Real.exp_le_one_iff]; exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ((show 0<z.re from p).le)) u

def monsoon (z:ℂ): Pe:=if p:z∈optimistic then BoundedContinuousFunction.ofNormedAddCommGroup (fun x=>clipExp z x) (by unfold clipExp;fun_prop) 1 (fun x=>most_hand z p x (by positivity)) else 0
private lemma monsoon_hit {z:ℂ}(p:z∈optimistic)(x:ℝ≥0): monsoon z x=clipExp z x:=by rw [monsoon,dif_pos p]; rfl
lemma monsoon_stamp(t:ℝ)(p:0<t)(x:ℝ≥0): monsoon (t:ℂ) x= Real.exp (-t*x):=by
 rw [monsoon_hit (assigned_ground p)]; unfold clipExp; push_cast; rfl
lemma monsoon_budget(z:ℂ)(p:z∈optimistic):‖monsoon z‖≤1:=BoundedContinuousFunction.norm_le_of_nonempty.mpr (fun i=> (monsoon_hit p i) ▸ most_hand z p (i:ℝ) i.property) -- orientation substitution

private lemma covers (z:ℂ)(p:z∈optimistic)(n:ℕ): ‖mantled n z-monsoon z‖≤ 2*Real.exp (-z.re*n):=by
 apply BoundedContinuousFunction.norm_le_of_nonempty.mpr; intro u; change ‖mantled n z u-monsoon z u‖≤ _; rw [monsoon_hit p,mantled_hit]; rcases le_total (u:ℝ) (n:ℝ) with h|h
 · rw [min_eq_left h,sub_self,norm_zero]; positivity
 rw [min_eq_right h]; refine (norm_sub_le ..).trans ?_; rw [clip_size,clip_size,two_mul]; gcongr _ + Real.exp ?_; nlinarith [show 0<z.re from p]
lemma monsoon_curve: AnalyticOnNhd ℂ monsoon optimistic:=by
 apply DifferentiableOn.analyticOnNhd _ current_open; apply chalk (F:=mantled) (l:=atTop) current_open _ (C:=1)
 · apply Eventually.of_forall; intro i z p; apply BoundedContinuousFunction.norm_le_of_nonempty.mpr; intro x; rw [mantled_hit]; exact most_hand z p _ (le_min (by positivity) (by positivity))
 · intro z p; apply tendsto_iff_norm_sub_tendsto_zero.mpr; refine squeeze_zero (fun _=>norm_nonneg _) (covers z p) ?_
   have ht:Tendsto (fun n:ℕ=> -z.re*n) atTop atBot:= (tendsto_const_mul_atBot_of_neg (neg_lt_zero.mpr (show 0 < z.re from p))).mpr tendsto_natCast_atTop_atTop
   simpa only [Function.comp_def,mul_zero] using (Real.tendsto_exp_atBot.comp ht).const_mul 2
 apply Eventually.of_forall; intro n; apply AnalyticOnNhd.differentiableOn; intro z _; unfold mantled
 apply AnalyticAt.comp (NormedSpace.exp_analytic _) (analyticAt_id.neg.smul analyticAt_const)
end YM.ConePrice.Storm

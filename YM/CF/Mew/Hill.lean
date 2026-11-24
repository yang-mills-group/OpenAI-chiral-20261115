import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Bourse
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Mew
open Function Set Metric Filter Complex MeasureTheory
open scoped Topology ContDiff BigOperators Matrix
variable {I E A:Type*} [Fintype I][DecidableEq I][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
abbrev Key(I:Type*):= I→ℂ
abbrev hill(I:Type*)[Fintype I]:Set (Key I):=closedBall (0:Key I) 1
abbrev rim: Set ℂ:=ball 0 1
lemma hill_i {z:Key I}:z∈hill I ↔ ∀ i,‖z i‖ ≤ 1:=(mem_closedBall_zero_iff.trans (pi_norm_le_iff_of_nonneg zero_le_one))
structure River (f:Key I→ E):Prop where
 shore:ContinuousOn f (hill I)
 slope(z:Key I)(p:z∈hill I)(i:I)(x:ℂ)(h:x∈ rim): DifferentiableAt ℂ (fun w=>f (update z i w)) x
variable {f g:Key I→E}{x y:Key I}
lemma fill_I(h:x∈ hill I)(i:I){u:ℂ}(hu: u∈closedBall (0:ℂ) 1): update x i u ∈ hill I:=hill_i.mpr (fun j=>by by_cases p:j=i; simpa [p] using mem_closedBall_zero_iff.mp hu; simpa [p] using (hill_i.mp h j))
lemma under_r(i:I)(u:Key I): Continuous (fun w=>update u i w):=(continuous_update (A:=fun _:I=>ℂ) i).comp (continuous_const.prodMk continuous_id)
lemma River.budget(h:River f):∃ C:ℝ, 0 ≤ C∧∀ i∈hill I, ‖f i‖ ≤ C:=by obtain ⟨C,V⟩:=((isCompact_closedBall ..).image_of_continuousOn h.shore.norm).bddAbove; refine ⟨max C 0,le_max_right ..,fun i hi=> ?_⟩; exact (V ⟨i,hi,rfl⟩).trans (le_max_left ..)
lemma River.circle(h:River f)(hx:x∈ hill I)(i:I): DiffContOnCl ℂ (fun w=>f (update x i w)) rim:= ⟨fun u p=>(h.slope _ hx i u p).differentiableWithinAt,(h.shore.comp (under_r i x).continuousOn (fun _ hy=> fill_I hx i hy)).mono closure_ball_subset_closedBall⟩
-- ∂ with cost one, stays on sector stamp
abbrev homeB(x:ℝ):ℂ:= circleMap 0 1 x
lemma home_q(x:ℝ): ‖homeB x‖=1:=by rw [homeB,norm_circleMap_zero,abs_one]
lemma homeC(x:ℝ):homeB x∈closedBall (0:ℂ) 1:=mem_closedBall_zero_iff.mpr (home_q x).le
abbrev roll:ℝ:=2*Real.pi
lemma roll_pos :0<roll:=mul_pos two_pos Real.pi_pos
abbrev sky: Measure ℝ:= ENNReal.ofReal roll⁻¹ • volume.restrict (Ioc 0 roll)
instance airy:IsProbabilityMeasure sky:=⟨by
 simp only [sky,Measure.smul_apply,Measure.restrict_apply MeasurableSet.univ,univ_inter,Real.volume_Ioc, sub_zero, smul_eq_mul]
 rw [← ENNReal.ofReal_mul (inv_pos.mpr roll_pos).le,inv_mul_cancel₀ roll_pos.ne', ENNReal.ofReal_one]⟩
section peel
-- Pin real normed? infer canonical instance NormedSpace.real via RestrictScalars? 
def cutI (f:Key I→E)(i:I)(v:Key I):E:=∫ θ:ℝ,(homeB θ)⁻¹ • f (update v i (homeB θ)) ∂sky
lemma mitt(h:River f)(u:x∈ hill I)(i:I): HasDerivAt (fun w=> f (update x i w)) (cutI f i x) 0:=by
 let g:ℂ→E:=fun w=> f (update x i w); have hh:= DiffContOnCl.deriv_eq_smul_circleIntegral (c:=(0:ℂ)) (R:=1) zero_lt_one (h.circle u i); let a:= (2 * Real.pi * Complex.I); -- coercion Real from 2*
 unfold circleIntegral at hh
 let Q(θ:ℝ):E:= (homeB θ)⁻¹ • g (homeB θ)
 have he(t:ℝ): deriv (circleMap 0 1) t • ((1/(circleMap 0 1 t-0)^2:ℂ) • f (update x i (circleMap 0 1 t)))=Complex.I • Q t:=by
    rw [deriv_circleMap, smul_smul, sub_zero]; unfold Q; rw [smul_smul]; apply congrArg (fun v:ℂ=> v • g (homeB t)); have hx: homeB t≠0:=norm_ne_zero_iff.mp (by rw [home_q]; norm_num); change homeB t*Complex.I * (1/homeB t^2)=_; field_simp
 change (∫ θ:ℝ in 0..roll, _)=(2* Real.pi * Complex.I) • deriv g 0 at hh
 simp_rw [he] at hh; rw [intervalIntegral.integral_smul] at hh
 let P:=∫ θ:ℝ in Ioc 0 roll, Q θ
 rw [intervalIntegral.integral_of_le roll_pos.le] at hh
 unfold cutI; change HasDerivAt g (∫ θ:ℝ,Q θ ∂sky) 0
 rw [sky,integral_smul_measure, ENNReal.toReal_ofReal (inv_pos.mpr roll_pos).le]
 suffices hk:(roll:ℝ)⁻¹ • P= deriv g 0 by change HasDerivAt g (roll⁻¹ • P) 0; rw [hk]; exact (h.slope _ u i _ (mem_ball_self zero_lt_one)).hasDerivAt
 have ht:P=(roll:ℝ) • deriv g 0:=by
    apply (smul_right_injective E Complex.I_ne_zero)
    change Complex.I • P= Complex.I • ((roll:ℂ) • _); rw [smul_smul, mul_comm]; change Complex.I • P= (↑roll * Complex.I) • _; unfold roll; push_cast; exact hh
 rw [ht,inv_smul_smul₀ roll_pos.ne']
lemma stayB (h:River f)(u:x∈ hill I)(i:I): Continuous (fun θ:ℝ=>(homeB θ)⁻¹ • f (update x i (homeB θ))):=( (continuous_circleMap _ _).inv₀ (fun x=>norm_ne_zero_iff.mp (by rw [← homeB,home_q]; norm_num))).smul (h.shore.comp_continuous ((under_r i x).comp (continuous_circleMap ..)) (fun θ=> fill_I u i (homeC _))) -- issue
end peel
end YM.CF.Mew

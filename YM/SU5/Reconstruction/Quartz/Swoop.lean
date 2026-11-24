import YM.SU5.Reconstruction.Quartz.HillGlass
set_option autoImplicit false
noncomputable section
namespace YM.Quartz.Ravin
open Function Set Filter MeasureTheory Metric Topology Complex
open scoped Topology NNReal ENNReal Complex ComplexOrder InnerProductSpace Classical Interval
lemma hor (a b c d:ℝ)(h:a≤b)(e:c≤d){F:ℂ→ℂ}(p:ContinuousOn F (Icc a b ×ℂ Icc c d))(q:DifferentiableOn ℂ F (Ioo a b ×ℂ Ioo c d)):
 (∫ x:ℝ in a..b,F (x+c*I)) - (∫ x:ℝ in a..b,F (x+d*I)) + I • (∫ y:ℝ in c..d,F (b+y*I))- I • (∫ y:ℝ in c..d,F (a+y*I))=0:= by
  apply Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn F ⟨a,c⟩ ⟨b,d⟩ _ _
  · exact (uIcc_of_le h).symm ▸ ((uIcc_of_le e).symm ▸ p) -- tune
  simpa only [min_eq_left h,max_eq_right h,min_eq_left e,max_eq_right e] using q
lemma countEdge (F:ℕ→ℝ→ℂ) (a b:ℝ)(f:ℝ→ℂ)(h:a≤b)(M:ℝ)(p:∀n,ContinuousOn (F n) (Icc a b))(q:∀n,∀ x∈Icc a b, ‖F n x‖≤M) (l:∀ x∈Ioc a b,Tendsto (fun n=> F n x) atTop (𝓝 (f x))):
    Tendsto (fun n=> ∫ x in a..b,F n x) atTop (𝓝 (∫ x in a..b, f x)):= by
 apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _=>M) _ _ intervalIntegrable_const _ <;> rw [uIoc_of_le h]
 · exact Eventually.of_forall fun n=> ((p n).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
 · exact Eventually.of_forall fun n=> ae_of_all _ (fun y p=> q n _ (Ioc_subset_Icc_self p))
 exact ae_of_all _ l
variable {F:ℕ→ℂ→ℂ}{M C:ℝ}(s:Studies F M C)
include s
local notation "v₀"=>1/(4*C)
variable {g:ℝ→ℂ} (t:∀ p:ℝ,Tendsto (fun n=> F n p) atTop (𝓝 (g p)))
include t
lemma decline (a b:ℝ)(p: -v₀ ≤a)(q:b≤v₀)(d:a≤b) : (∫ x in a..b, g x)=0:= by
 let f(n:ℕ)(x y:ℝ):= F n ((x:ℂ)+y*I)
 let U:= dome a b
 let W:= spin a b
 have hw : U⊆ dome (-v₀) v₀:= inter_subset_inter_left _ (preimage_mono (Icc_subset_Icc p q)); have hu: U⊆ D:= fun z hz=> ⟨slide s z.re ((hw hz).1),hz.2⟩
 have hq(n):DifferentiableOn ℂ (F n) W:= by
    apply (s.polish n).mono; rintro z ⟨⟨hx,hy⟩,h⟩; exact ⟨⟨((slide s a ⟨p,d.trans q⟩).1).trans_lt hx,hy.trans_le (slide s b ⟨p.trans d,q⟩).2⟩,h⟩
 have k(n):ContinuousOn (F n) U:=(s.reads n).mono hu
 have hv(n)(z:ℂ)(v:z∈U): ‖F n z‖≤M:= (subsidence s z (hw v) n).trans ((mul_le_of_le_one_right s.M0 <| Real.exp_le_one_iff.mpr <| mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (show 0≤sightParam n from by unfold sightParam; positivity)) (div_nonneg v.2.1 (by norm_num))))
 have e(x y:ℝ)(t:x∈ Icc a b)(p:y∈ Icc 0 κ): ((x:ℂ)+(y:ℂ)*I)∈ U:= by unfold U dome; simp only [mem_reProdIm,add_re, mul_re, ofReal_re,I_re, ofReal_im,I_im,mul_zero,mul_one,sub_zero,add_zero, add_im, mul_im,zero_add]; exact ⟨t,p⟩
 have hF(n:ℕ)(y:ℝ)(p:y∈ Icc 0 κ):ContinuousOn (fun x:ℝ=> f n x y) (Icc a b):= (k n).comp (by fun_prop) (fun x k=>e x y k p) -- tune complex combo
 have k1:(κ:ℝ)∈ Icc (0:ℝ) κ:= ⟨potential.le,le_rfl⟩; have k2:(0:ℝ)∈Icc (0:ℝ) κ:= ⟨le_rfl,potential.le⟩
 let top(n:ℕ):=∫ x:ℝ in a..b, f n x κ; let b0(n:ℕ):=∫ x:ℝ in a..b, f n x 0; let MM(x:ℝ)(n:ℕ):=∫ v:ℝ in 0..κ,f n x v -- shadow M! rename
 have eA: Tendsto b0 atTop (𝓝 (∫ x in a..b,g x)):=countEdge _ a b g d _ (fun n=>hF n _ k2) (fun n x p=> hv n _ (e x _ p k2)) (fun x p=>by simpa [f] using t x)
 have hz(n:ℕ) : b0 n-top n+I • MM b n-I • MM a n=0:=hor a b 0 κ d potential.le (k n) (hq n)
 have eB:Tendsto top atTop (𝓝 0):=by
    simpa only [intervalIntegral.integral_zero] using countEdge (fun n x=> f n x κ) a b (fun x=>(0:ℂ)) d _ (fun n=>hF n _ k1) (fun n x p=>hv n _ (e x _ p k1)) (fun x p=> decreases s _ (hw (e x _ (Ioc_subset_Icc_self p) k1)) (by simp [Real.pi_pos] -- simp /2 etc
    ))
 have bM(x:ℝ)(p:x∈Icc a b): Tendsto (MM x) atTop (𝓝 0):=by
    simpa only [intervalIntegral.integral_zero] using countEdge (fun n y=>f n x y) 0 κ (fun x=>(0:ℂ)) potential.le _ (fun n=> (k n).comp (by fun_prop) (fun y q=>e x y p q)) (fun n y q=> hv n _ (e x y p q)) (fun y q=> decreases s _ (hw (e x y p (Ioc_subset_Icc_self q))) (by simpa using q.1))
 refine tendsto_nhds_unique eA ?_; apply Tendsto.congr' (f₁:= fun i:ℕ=> top i + I • MM a i - I • MM b i) (Eventually.of_forall (fun x=> (?_:_=b0 x))) (by simpa only [smul_zero,add_zero,sub_self] using (eB.add ((tendsto_const_nhds (x:=I)).smul (bM a ⟨le_rfl,d⟩))).sub ((tendsto_const_nhds (x:=I)).smul (bM b ⟨d,le_rfl⟩))) -- notation parameters
 change top x+ I • MM a x-I • MM b x=b0 x; have hp:= hz x; linear_combination -hp
lemma prize (D0:Continuous g) : g 0=0:= by
 let h(x:ℝ):=∫ y in 0..x,g y
 have hx : h=ᶠ[𝓝 0] 0:= by
    have hp: 0< C:= lt_of_lt_of_le zero_lt_one s.C0; have hz: 0<v₀:=by positivity
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hz) hz] with x p
    unfold h; rcases le_total 0 x with w|w; exact decline s t 0 x (by linarith) p.2.le w
    rw [intervalIntegral.integral_symm,decline s t x 0 p.1.le hz.le w]; simp
 have hk := ((D0.integral_hasStrictDerivAt 0 0).hasDerivAt.congr_of_eventuallyEq hx.symm)
 exact hk.unique (hasDerivAt_const (𝕜:=ℝ) 0 0)
end YM.Quartz.Ravin

import YM.SU5.FiniteGaugeData.Galope.Tambour
import Mathlib.Analysis.Convex.Integral
import Mathlib.Probability.Distributions.Gaussian.Fernique
/-! # Lipschitz payment with many Gaussian marks, interpolation estimate. 

  Keep explicit constants uniform even over the inspections of cameras, lag and period volumes.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 20000
set_option linter.flexible false
set_option quotPrecheck false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Lapis
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology InnerProductSpace Matrix ContDiff BigOperators NNReal ENNReal
namespace Motion
open Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {h C : ℝ} {F : E → ℝ}
local notation "V" => E × E
local notation "μ" => stdGaussian E
local notation "W" => (stdGaussian E).prod (stdGaussian E)
def bill (L: ℝ):ℝ := (π/2)^2*L^2/2
abbrev america (L:ℝ) := Real.exp (bill L)
abbrev height (x:E)(F:E→ℝ):=Real.exp (F x - ∫ k,F k∂stdGaussian E)
def smooth(F:E→ℝ)(v:V):ℝ:= Real.exp (F v.2-F v.1)
abbrev pathR (x:V)(t:ℝ): E×E:= ContinuousLinearMap.rotation (t*(π/2)) x
-- path from x.1 to x.2, bill paid along tangent.
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma windR(x:V)(t:ℝ): HasDerivAt (fun t:ℝ=> (pathR x t).1) ((π/2:ℝ) • (pathR x t).2) t:=by
  let q:=(π/2:ℝ); let f(t:ℝ):=t*q; have hp : HasDerivAt f q t := by simpa using (hasDerivAt_id' t).mul_const q
  have hw:= (hp.cos.smul_const x.1).add (hp.sin.smul_const x.2)
  simp only [pathR,ContinuousLinearMap.rotation_apply]; convert! hw using 1; unfold f q
  simp only [smul_add,smul_smul]; rw [_root_.mul_comm (π/2),_root_.mul_comm (π/2)] -- tune
abbrev diffR(F:E→ℝ)(x:V):ℝ:= (π/2:ℝ) * (fderiv ℝ F x.1 x.2)
abbrev wind(F:E→ℝ)(x:V)(t:ℝ):ℝ:= diffR F (pathR x t)
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma pay_diff(f:ContDiff ℝ 1 F): Continuous (diffR F):=by unfold diffR; exact continuous_const.mul (((f.continuous_fderiv (by norm_num)).comp continuous_fst).clm_apply continuous_snd)
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma wind_c(f:ContDiff ℝ 1 F): Continuous (uncurry (wind F)):=by
 have he:Continuous (fun x: (E×E)×ℝ => pathR x.1 x.2):=by simp only [pathR,ContinuousLinearMap.rotation_apply]; fun_prop
 exact (pay_diff f).comp he
abbrev staple:Measure ℝ:= volume.restrict (Set.Ioc (0:ℝ) 1)
local instance : IsProbabilityMeasure staple := ⟨by simp [staple]⟩
lemma mail (x:V)(f:ContDiff ℝ 1 F) : smooth F x ≤ ∫ t,exp (wind F x t)∂staple:=by
 let u:= wind F x; have h:Continuous u:=by
    change Continuous ((uncurry (wind F)) ∘ (Prod.mk x : ℝ → _)); exact (wind_c f).comp (Continuous.prodMk continuous_const continuous_id)
 have he(t:ℝ): HasDerivAt (fun t=> F (pathR x t).1) (u t) t:=by simpa! only [u,wind,diffR,Function.comp_def,map_smul, smul_eq_mul] using (f.differentiable (by norm_num) (pathR x t).1).hasFDerivAt.comp_hasDerivAt t (windR x t)
 have hu : F x.2 - F x.1=∫ t, u t∂staple:=by
    unfold staple; rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun i hi=> he i) (h.intervalIntegrable ..)]; simp [pathR,ContinuousLinearMap.rotation_apply] -- tune
 unfold smooth; rw [hu]; exact convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ (Eventually.of_forall fun x=>Set.mem_univ _) (h.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self) ((Real.continuous_exp.comp h).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self) -- tune
lemma postcard (L: E→L[ℝ]ℝ) (t:ℝ): let f:=fun x:E => exp (t*L x); let r:=exp (‖L‖^2*t^2/2); Integrable f μ ∧ (∫ x, f x∂μ)=r:=by
 intro f r; let q:= ((‖L‖^2):ℝ).toNNReal; have h: MeasurePreserving L μ (gaussianReal 0 q):= ⟨L.continuous.measurable,by rw [IsGaussian.map_eq_gaussianReal L, integral_strongDual_stdGaussian, variance_dual_stdGaussian]⟩; refine ⟨h.integrable_comp_of_integrable (integrable_exp_mul_gaussianReal t),?_⟩
 change mgf (fun y=> L y) μ t= _; rw [mgf_gaussianReal h.map_eq]; simp [r,q]
lemma mercury (f:ContDiff ℝ 1 F)(u:∀ x, ‖fderiv ℝ F x‖≤ C) : let g:= Real.exp ∘ diffR F; Integrable g W ∧ (∫ x,g x∂W)≤ america C :=by
 intro g; let G:E→ℝ:=fun x=>exp (bill ‖fderiv ℝ F x‖); have he(x:E): Integrable (fun y=>g (x,y)) μ ∧ (∫ y,g (x,y)∂μ)=G x:=by obtain ⟨r,v⟩:=postcard (fderiv ℝ F x) (π/2); refine ⟨r,Eq.trans v ?_⟩; unfold G bill; rw [_root_.mul_comm (‖fderiv ℝ F x‖^2)]
 have hh(x:V):0≤g x:= (Real.exp_pos _).le; have ha(x:E): G x ≤ america C:= exp_monotone (by unfold bill; gcongr; exact u x)
 have hp:Integrable G μ:= by
    apply Integrable.of_bound (C:=america C) ?_ (Eventually.of_forall (fun x=> show ‖G x‖ ≤ america C by rw [Real.norm_of_nonneg (show 0 ≤ G x from (exp_pos _).le)]; exact ha x)); unfold G bill; have h:= f.continuous_fderiv (by norm_num); fun_prop
 have hz : Integrable g W:= (integrable_prod_iff ((continuous_exp.comp (pay_diff f)).measurable.aestronglyMeasurable)).2 ⟨Eventually.of_forall (fun x:E=> (he x).1), hp.congr (Eventually.of_forall (fun x:E=>by change G x=∫ y, ‖g (x,y)‖ ∂μ; simp_rw [Real.norm_of_nonneg (hh _)]; exact (he x).2.symm))⟩
 refine ⟨hz,?_⟩; rw [integral_prod _ hz]
 exact (integral_mono (hz.integral_prod_left) (integrable_const _) (fun i => le_trans (le_of_eq (he i).2) (ha i))).trans_eq (by simp)
lemma mellow (f:ContDiff ℝ 1 F)(u:∀ x, ‖fderiv ℝ F x‖≤ C) (t:ℝ) : let g':= fun p:V=> exp (wind F p t); Integrable g' W ∧ (∫ p,g' p∂W) ≤ america C :=by
 intro g'; let g:= Real.exp ∘ diffR F; obtain ⟨T,v⟩:=mercury f u; let L:= ContinuousLinearMap.rotation (E:=E) (t*(π/2))
 have ht: MeasurePreserving L W W:=⟨L.continuous.measurable, IsGaussian.map_rotation_eq_self (by simp) _⟩
 apply And.intro (ht.integrable_comp_of_integrable T); refine le_trans (Eq.le ?_) v; rw [show (∫ v:V,(Real.exp ∘ diffR F) v∂W)=∫ v,g v∂(Measure.map L W) by rw [ht.map_eq]]; have he : AEStronglyMeasurable g (Measure.map L W) := ht.map_eq.symm ▸ T.aestronglyMeasurable; exact (integral_map ht.measurable.aemeasurable he).symm -- annotate
lemma prism (f:ContDiff ℝ 1 F)(u:∀ x, ‖fderiv ℝ F x‖≤ C)(p:∀ x, ‖F x‖≤ h) :
 (∫ z,smooth F z ∂W) ≤ america C :=by
 let P(z:V×ℝ):= exp (wind F z.1 z.2); let ν := (stdGaussian E).prod (stdGaussian E) |>.prod staple -- not parse
 have hm: AEStronglyMeasurable P ν := (Real.continuous_exp.comp (wind_c f)).measurable.aestronglyMeasurable; have hP(z:V×ℝ): ‖P z‖=P z:=Real.norm_of_nonneg (exp_pos _).le; let g(t:ℝ):= (∫ v : V, ‖P (v,t)‖∂W)
 have hy(t:ℝ): g t= ∫ v, P (v,t)∂W:=by unfold g; simp_rw [hP]
 have hx: Integrable P ν:= (integrable_prod_iff' hm).2 ⟨ae_of_all staple (fun t=> (mellow f u t).1), (by
    apply Integrable.of_bound (C:=america C)
    · apply hm.prod_swap.norm.integral_prod_right' -- maybe timeout
    apply ae_of_all; intro t; change ‖g t‖≤_; rw [Real.norm_of_nonneg (show 0≤g t from integral_nonneg (fun x=>norm_nonneg _)),hy]; exact (mellow f u t).2 )⟩
 let Y:=exp (2*h)
 have he:Integrable (smooth F) W:=by
    apply Integrable.of_bound (C:=Y)
    · exact ((Real.continuous_exp.comp ((f.continuous.comp continuous_snd).sub (f.continuous.comp continuous_fst))).measurable).aestronglyMeasurable
    apply ae_of_all; intro z; unfold smooth; rw [Real.norm_of_nonneg (exp_pos _).le]; apply Real.exp_monotone; linarith only [neg_le_of_abs_le (p z.1), le_of_abs_le (p z.2)] -- tune p uses ‖
 have hh:let Z:=(∫ v : V, (∫ t,P (v,t)∂staple) ∂W); Z ≤ america C:=by
    dsimp only; rw [← integral_prod P hx, integral_prod_symm P hx]; apply (integral_mono hx.integral_prod_right (integrable_const (america C)) (fun x=> (mellow f u x).2)).trans_eq; simp
 exact (integral_mono he hx.integral_prod_left (mail · f)).trans hh
variable {X:Type*}[MeasurableSpace X]{ν : Measure X} [IsFiniteMeasure ν] {l:X→ℝ}
lemma gaol (p:Measurable l)(u:∀ x,l x≤h) : Integrable (exp∘l) ν:=Integrable.of_bound ((Real.continuous_exp.measurable.comp p).aestronglyMeasurable) (exp h) (ae_of_all ν (fun x=>le_trans (Real.norm_of_nonneg (show 0≤exp (l x) from (exp_pos _).le)).le (Real.exp_monotone (u x)))) -- spell
lemma starlet (f:ContDiff ℝ 1 F)(p:∀ x, ‖F x‖≤ h) : Integrable F μ ∧ Integrable (exp ∘ F) μ :=⟨Integrable.of_bound f.continuous.measurable.aestronglyMeasurable h (ae_of_all _ p),gaol f.continuous.measurable (fun x=>le_of_abs_le (p x))⟩
theorem peak (f:ContDiff ℝ 1 F)(u:∀ x, ‖fderiv ℝ F x‖ ≤ C)(p:∀ x, ‖F x‖≤ h) : (∫ x, exp (F x)∂μ) ≤ exp ( (∫ x, F x∂μ)+ bill C) :=by
 let A:=∫ x: E, F x∂μ; let Y:=∫ x: E,exp (-F x)∂μ; let T:=∫ x:E,exp (F x)∂μ; have ht0:0≤T:= integral_nonneg (fun i=> (Real.exp_pos _).le); let g:= -F; obtain ⟨hg,hG⟩:= starlet (show ContDiff ℝ 1 g from f.neg) (fun x=> by change ‖-F x‖≤ h; exact (norm_neg _).le.trans (p x)); have ht : Y*T ≤ america C:=by
    have he(v:V): smooth F v=(exp∘g) v.1 * exp (F v.2):=by unfold smooth; rw [show F v.2-F v.1=g v.1+F v.2 from by unfold g; dsimp; linarith only,Real.exp_add]; rfl
    have hz:=prism f u p; simp_rw [he] at hz; rw [integral_prod_mul (exp∘g) (fun i=>exp (F i))] at hz; exact hz -- tune comp
 have hv : exp (-A) ≤ Y:=by
    have he:= convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ (Eventually.of_forall (fun x:E=>Set.mem_univ _)) hg hG
    change exp (∫ x,g x∂μ)≤_ at he -- fix
    rw [show (∫ x,g x∂μ)=-A from integral_neg F] at he; exact he
 have hk:= (mul_le_mul_of_nonneg_right hv ht0).trans ht; change T≤ exp (A+bill C); rw [Real.exp_add]; calc
    T = exp A * (exp (-A) * T):=by rw [←mul_assoc, ←Real.exp_add,add_neg_cancel]; simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hk (exp_pos _).le
end Motion
end YM.SU5.FiniteGaugeData.Lapis
#print axioms YM.SU5.FiniteGaugeData.Lapis.Motion.peak

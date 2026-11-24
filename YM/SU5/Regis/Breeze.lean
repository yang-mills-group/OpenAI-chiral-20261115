import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
/-!
# Cost for smooth bounded test insertions vs Gaussian pressure

Pisier rotation trick. Dimension-free cost. No infinite-dim handling needed for this
application. Might consider extension to unbounded/nonsmooth f by approximation later.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.Regis
open Function Real ProbabilityTheory MeasureTheory Filter
open scoped ContDiff Topology ENNReal BigOperators Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (f:E→ℝ) (y t C :ℝ)
local notation "μ" => stdGaussian E
local notation "Φ" => fun x:E=> f x
local notation "B" => (μ).prod μ
variable {γ : Type*} [MeasurableSpace γ] (L : E →L[ℝ] ℝ) (ν : Measure γ)
lemma bree (ν : Measure γ) [IsFiniteMeasure ν] (φ:γ→ℝ) {a:ℝ} (p: Measurable φ) (t:∀ i,|φ i|≤ a) : Integrable φ ν:=by
 refine (integrable_const («μ»:=ν) a).mono' p.aestronglyMeasurable (ae_of_all _ fun i=>?_); exact t i
lemma puff (ν : Measure γ) [IsFiniteMeasure ν] (φ:γ→ℝ) (q:ℝ) {a:ℝ} (p: Measurable φ) (t:∀ i,|φ i|≤ a) : Integrable (fun i=> exp (q * φ i)) ν:=by
 refine bree _ _ (a:=exp (|q| *a)) (by fun_prop) (fun i=>?_); rw [abs_of_pos (exp_pos _)]; apply exp_monotone; exact (le_abs_self _).trans ((abs_mul ..).trans_le (mul_le_mul_of_nonneg_left (t i) (abs_nonneg _)))
lemma exp_linear : mgf (⇑L) (stdGaussian E) t= exp (‖L‖^2*t^2/2):=by
 rw [mgf_gaussianReal (IsGaussian.map_eq_gaussianReal («μ»:=μ) L), integral_strongDual_stdGaussian, variance_dual_stdGaussian]; rw [Real.coe_toNNReal _ (by positivity)]; ring_nf
section
variable {R M : ℝ}
variable (b : ∀ x, |f x| ≤ M) (hf : ContDiff ℝ 1 f) (l : ∀ x, ‖fderiv ℝ f x‖ ≤ R)
include b hf l
local notation "L" => (Real.pi/2)
-- RHS for Pisier trick
abbrev pin (x:E×E) := exp (t * L * fderiv ℝ f x.1 x.2)
omit b
lemma pin_b (x:E) : (∫ y:E,pin f t (x,y) ∂μ) ≤ exp (R^2*(t*L)^2/2) := by
 change mgf (⇑(fderiv ℝ f x)) μ (t*L) ≤ _
 rw [exp_linear]; gcongr; exact l x
lemma pin_meas : Continuous (pin f t):= by unfold pin; fun_prop (disch:=first | exact hf.continuous_fderiv (by norm_num))
lemma pin_int : Integrable (pin f t) B:=by
 refine (integrable_prod_iff (pin_meas f t hf l).aestronglyMeasurable).2 ⟨ae_of_all _ fun x : E=>?_ ,?_⟩
 · change Integrable (fun y : E=> Real.exp ((t*L) *((fderiv ℝ f x) y))) μ; apply (mgf_pos_iff (X:= ⇑(fderiv ℝ f x)) (t:=t*L)).1; rw [exp_linear]; exact Real.exp_pos _
 refine (integrable_const («μ»:=μ) (exp (R^2*(t*L)^2/2))).mono' ?_ (ae_of_all _ fun x=>?_)
 · exact (Continuous.aestronglyMeasurable ((pin_meas f t hf l).norm)).integral_prod_right'
 have hx(y:E):0≤ pin f t (x,y):=(exp_pos _).le
 rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _=> norm_nonneg _))]
 simp_rw [Real.norm_eq_abs, abs_of_nonneg (hx _)]; exact pin_b f t hf l _
lemma pin_goal : (∫ x,pin f t x ∂B) ≤ exp (R^2*(t*L)^2/2):= by
 rw [integral_prod _ (pin_int f t hf l)]; refine (integral_mono (pin_int f t hf l|>.integral_prod_left) (integrable_const _) (fun x=>pin_b f t hf l x)).trans_eq ?_; simp
local notation "α" => volume.restrict (Set.Ioc (0:ℝ) 1)
local instance : IsProbabilityMeasure (volume.restrict (Set.Ioc (0:ℝ) 1)) := ⟨by simp⟩
abbrev wave (q:ℝ)(x:E×E):= ContinuousLinearMap.rotation (q*L) x
lemma wavesheet (q:ℝ) : MeasurePreserving (wave (E:=E) q) B B := ⟨by unfold wave; fun_prop,IsGaussian.map_rotation_eq_self (by exact integral_id_stdGaussian) (q*L)⟩
abbrev ride (q:ℝ)(x:E×E):= t * L * (fderiv ℝ f (wave q x).1) (wave q x).2
abbrev rider (q:ℝ) (x:E×E):= pin f t (wave q x)
lemma ride_cont : Continuous (uncurry (ride f t)):=by unfold uncurry ride wave; simp_rw [ContinuousLinearMap.rotation_apply]; fun_prop (disch:=first | exact hf.continuous_fderiv (by norm_num))
omit l in
lemma wave_path (x:E×E) (q:ℝ) : HasDerivAt (fun q=> t * f (wave q x).1) (ride f t q x) q:=by
 let s:= q*L; have h: HasDerivAt (fun q':ℝ=> q'*L) L q:=by simpa using (hasDerivAt_id' q).mul_const L
 have hp: HasDerivAt (fun q=>(wave q x).1) (L • (wave q x).2) q:=by
    simp_rw [wave,ContinuousLinearMap.rotation_apply,smul_add,smul_smul]; convert! (h.cos.smul_const (F:=E) x.1).add (h.sin.smul_const (F:=E) x.2) using 1; simp [mul_comm]
 convert! (((hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt q hp).const_mul t) using 1; rw [map_smul]; simp only [ride, smul_eq_mul,mul_assoc]
lemma rider_cost (x:E×E) : exp (t*(f x.2-f x.1)) ≤ ∫ i, rider f t i x ∂α:=by
 let g:= fun q=>ride f t q x; have he: Continuous g := by unfold g ride wave; simp_rw [ContinuousLinearMap.rotation_apply]; fun_prop (disch:=first | exact hf.continuous_fderiv (by norm_num))
 have h : ∫ i,g i ∂α=t*(f x.2-f x.1):=by
    rw [←intervalIntegral.integral_of_le zero_le_one]; unfold g; rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun i _=> wave_path f t hf x i) (he.intervalIntegrable ..)]; simp [wave, ContinuousLinearMap.rotation_apply, mul_sub]
 rw [← h]; refine convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ (ae_of_all _ fun _=> Set.mem_univ _) ?_ ?_
 · exact he.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
 exact (continuous_exp.comp he).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
lemma movement (a:ℝ) : (∫ x,rider f t a x ∂B)=∫ x,pin f t x∂B:=by
 let R':=wavesheet f hf l a
 refine Eq.symm (?_); conv_lhs=>arg 1; rw [←R'.map_eq]
 exact integral_map (by unfold wave; fun_prop) (pin_meas f t hf l|>.aestronglyMeasurable)
lemma rider_int : Integrable (uncurry (rider f t)) ((α).prod B):=by
 let C:= uncurry (rider f t); have hC:Continuous C:= continuous_exp.comp (ride_cont f t hf l)
 refine (integrable_prod_iff hC.aestronglyMeasurable).mpr ⟨ae_of_all _ fun x=>(wavesheet f hf l x).integrable_comp_of_integrable (pin_int f t hf l),?_⟩
 change Integrable (fun i=> ∫ x, ‖rider f t i x‖ ∂B) α; simp_rw [Real.norm_eq_abs, abs_of_pos ((show ∀ i:ℝ, ∀ x, 0 < rider f t i x from fun i x=>exp_pos _) _ _), movement f t hf l]; exact integrable_const _
abbrev chance (x:E×E) := exp (t*(f x.2-f x.1))
include b
lemma chance_int : Integrable (chance f t) B:=by
 refine puff _ (fun x:E×E=> f x.2-f x.1) t (a:=M+M) ((hf.continuous.comp continuous_snd).sub (hf.continuous.comp continuous_fst)|>.measurable) (fun i=>?_)
 exact (abs_sub _ _).trans (add_le_add (b _) (b _))
lemma joint_goal : (∫ x,chance f t x∂B) ≤ exp (R^2*(t*L)^2/2):=by
 let C:= exp (R^2*(t*L)^2/2); let G:= rider_int f t hf l
 refine le_trans (b:= ∫ x,(∫ y,rider f t y x ∂α)∂B) (integral_mono (chance_int f t b hf l) G.integral_prod_right (fun _=> rider_cost f t hf l _)) ?_
 change (∫ x, (∫ y, (uncurry (rider f t)) (y,x)∂α)∂B) ≤ _
 rw [←integral_prod_symm _ G, integral_prod _ G]
 change (∫ y,(∫ x,rider f t y x∂B) ∂α) ≤ C
 simp_rw [movement f t hf l]; simp only [integral_const, probReal_univ,one_smul]; exact pin_goal f t hf l
lemma swindle (y:E) : exp (t*(f y-∫ x,f x ∂μ))≤ ∫ x,chance f t (x,y)∂μ:=by
 let g:=fun x=> f y-f x; have ht: Continuous g:=continuous_const.sub hf.continuous; let h(x:E): |g x| ≤ M+M:= (abs_sub ..).trans (add_le_add (b _) (b _)); let G:= fun q=> t * g q; have hz: ∫ x,G x∂μ=t* (f y-∫ x,f x ∂μ):=by
    unfold G g; rw [integral_const_mul, integral_sub (integrable_const _) (bree _ _ hf.continuous.measurable b)]; simp
 rw [←hz]; exact convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ (ae_of_all _ fun _=> Set.mem_univ _) ((bree _ _ ht.measurable h).const_mul _) (puff _ _ _ ht.measurable h)
theorem gale : mgf f (stdGaussian E) t ≤ exp (t*(∫ x,f x ∂stdGaussian E)+R^2*(t*L)^2/2):=by
 let h:= puff μ f t hf.continuous.measurable b; let z:=∫ x, f x∂μ; let w:=t*z; refine (mul_le_mul_iff_right₀ (exp_pos (-w))).1 ?_
 unfold mgf
 rw [←integral_const_mul, ← Real.exp_add]
 change ((∫ x:E, exp (-w)* exp (t*f x)∂μ)) ≤ _
 simp_rw [←exp_add, show ∀ x:E,-w+t*f x=t*(f x-z) from fun x=>by unfold w; ring]
 rw [show -w+_= R^2*(t*L)^2/2 from (by unfold w z; ring)]
 have w1:= chance_int f t b hf l; let w2:= joint_goal f t b hf l; apply le_trans (b:= ∫ x,chance f t x∂B) _ w2; rw [integral_prod_symm _ w1]; apply integral_mono _ w1.integral_prod_right (fun x=> swindle f t b hf l x)
 have hm: ‖z‖ ≤ M:= by simpa only [probReal_univ,mul_one] using (norm_integral_le_of_norm_le_const (f:=f) (C:=M) (ae_of_all μ (fun x=> b x)))
 exact puff μ _ _ ((hf.continuous.sub continuous_const).measurable) (fun i=>(abs_sub ..).trans (add_le_add (b i) hm))
end
end YM.Regis
#check YM.Regis.gale
#print axioms YM.Regis.gale

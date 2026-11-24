import YM.CF.Buffered.Borel
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Cyclic trace = Hilbert space trace

We use finite measures (channel counter × pack probability in the
application), bounded Borel kernels. Products of two kernels have the
ordinary trace along any Hilbert basis of L². `trace` is still the cyclic
kernel trace; its definition needs no choice of basis.
-/
set_option autoImplicit false
set_option maxHeartbeats 280000
noncomputable section
namespace YM.CF.Buffered.HS
open scoped BigOperators ENNReal Topology InnerProductSpace
open Push.SectorMeasure Function Lattice RG MeasureTheory NormedSpace Filter Finset
variable {X : Type*} [MeasurableSpace X] {K U V : X×X → ℂ}
def dual (K : X×X → ℂ) (p : X×X) := star (K p.swap)
omit [MeasurableSpace X] in
lemma dual_dual : dual (dual K)=K := funext fun p=> by simp [dual]
lemma envDual (h : Envelope K) : Envelope (dual K) := Girt.pole_w _ star continuous_star (Env.along h measurable_swap)
variable (μ : Measure X) [IsFiniteMeasure μ]

-- bounded kernel and its Hilbert representative
def trace (U V : X×X → ℂ) : ℂ := ∫ x, U x* V x.swap ∂μ.prod μ
abbrev Hilb := Lp ℂ 2 μ
private def factorM := ((μ Set.univ)^(2:ℝ)⁻¹ : ℝ≥0∞).toReal
omit [IsFiniteMeasure μ] in
private lemma factor_nonneg : 0 ≤ factorM μ := ENNReal.toReal_nonneg
private lemma normBound {f : X → ℂ} (h : MemLp f 2 μ) {C : ℝ} (hp : 0≤C)
   (hc : ∀ x : X, ‖f x‖ ≤ C) : ‖MemLp.toLp _ h‖ ≤ factorM μ*C := by
  rw [Lp.norm_toLp]
  have v := ENNReal.toReal_mono (b:=μ Set.univ^(2:ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal C) (by finiteness) (eLpNorm_le_of_ae_bound (ae_of_all μ hc))
  unfold factorM; simpa [ENNReal.toReal_mul, hp] using v
private def cap (h : Envelope K) := max 0 h.cost.choose
private lemma capnonneg (h : Envelope K) : 0≤ cap h := le_max_left ..
private lemma lecap (h : Envelope K) (x) : ‖K x‖ ≤ cap h := (h.cost.choose_spec x).trans (le_max_right ..)

def evaluate (K : X×X → ℂ) (f : Hilb μ) (x : X) : ℂ := ∫ y, K (x,y) * f y ∂μ
lemma eval_meas (h : Envelope K) (f : Hilb μ) : StronglyMeasurable (evaluate μ K f) :=
  StronglyMeasurable.integral_prod_right' ((h.meas.mul ((Lp.stronglyMeasurable f).measurable.comp measurable_snd)).stronglyMeasurable : StronglyMeasurable fun p => K p * f p.2)
private lemma memsec (h : Envelope K) (x:X) : MemLp (fun y=> star (K (x,y))) 2 μ :=
  MemLp.of_bound (continuous_star.measurable.comp (h.meas.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable _ (Eventually.of_forall fun y=> by rw [norm_star]; exact lecap h _)
private def sec (h : Envelope K) (x:X) : Hilb μ := MemLp.toLp _ (memsec μ h x)
private lemma evalInner (h : Envelope K) (f : Hilb μ) (x:X) : evaluate μ K f x = ⟪sec μ h x,f⟫_ℂ := by
  rw [L2.inner_def]; refine integral_congr_ae (((memsec μ h x).coeFn_toLp).mono ?_)
  intro p h; dsimp only; rw [RCLike.inner_apply, sec, h]; simp [mul_comm]
private lemma sec_bound (h : Envelope K) (x:X) : ‖sec μ h x‖ ≤ factorM μ*cap h :=
  normBound μ (memsec μ h x) (capnonneg h) (fun p=> by rw [norm_star]; exact lecap ..)
private lemma eval_bound (h : Envelope K) (f : Hilb μ) (x : X) : ‖evaluate μ K f x‖ ≤ factorM μ*cap h*‖f‖ := by
  rw [evalInner μ h]; exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (sec_bound μ h x) (norm_nonneg _))
lemma evalLp (h : Envelope K) (f : Hilb μ) : MemLp (evaluate μ K f) 2 μ := MemLp.of_bound (eval_meas μ h f).aestronglyMeasurable _ (Eventually.of_forall (eval_bound μ h f))
private def plain (h : Envelope K) : Hilb μ →ₗ[ℂ] Hilb μ where
  toFun f := MemLp.toLp _ (evalLp μ h f)
  map_add' f g:= by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (MemLp.toLp _ (evalLp μ h f)) (MemLp.toLp _ (evalLp μ h g)),(evalLp μ h (f+g)).coeFn_toLp, (evalLp μ h f).coeFn_toLp,(evalLp μ h g).coeFn_toLp] with x hx ha hb hc
    simp only [hx,ha,Pi.add_apply,hb,hc,evalInner μ h,inner_add_right]
  map_smul' c f:= by
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul c (MemLp.toLp _ (evalLp μ h f)),(evalLp μ h f).coeFn_toLp,(evalLp μ h (c•f)).coeFn_toLp] with x hx ha hb
    simp only [RingHom.id_apply, hx,Pi.smul_apply,ha,hb,smul_eq_mul,evalInner μ h,inner_smul_right]

def ofKernel (h : Envelope K) : Hilb μ →L[ℂ] Hilb μ := (plain μ h).mkContinuous (factorM μ*(factorM μ*cap h)) (fun x=> by
  simpa only [plain, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc] using (normBound μ (evalLp μ h x) (mul_nonneg (mul_nonneg (factor_nonneg μ) (capnonneg h)) (norm_nonneg _)) (eval_bound μ h x)))
lemma ofKernel_apply (h : Envelope K) (f : Hilb μ) : ((ofKernel μ h) f).val =ᵐ[μ] evaluate μ K f := (evalLp μ h f).coeFn_toLp

local notation "⟪" x "," y "⟫" => inner ℂ x y

lemma hilbertAdjoint (h : Envelope K) : ofKernel μ (envDual h) = (ofKernel μ h).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff ..).2; intro f g
  let t (x y : X) := K (x,y) * (star (f x) * g y)
  have hr : Integrable (fun x => star (f x)) μ := ((MemLp.integrable (by norm_num) (Lp.memLp f)).norm).mono' (continuous_star.measurable.comp (Lp.stronglyMeasurable f).measurable).aestronglyMeasurable (Eventually.of_forall fun a=> (norm_star _).le)
  have hi : Integrable (uncurry t) (μ.prod μ) :=
   Integrable.bdd_mul (hr.mul_prod (MemLp.integrable (by norm_num) (Lp.memLp g))) h.meas.aestronglyMeasurable (Eventually.of_forall (lecap h))
  rw [L2.inner_def,L2.inner_def]; calc
    _ = ∫ y, ∫ x, t x y ∂μ ∂μ := integral_congr_ae ((ofKernel_apply μ (envDual h) f).mono fun y hy=> by
          dsimp only
          rw [RCLike.inner_apply, hy]; dsimp only [evaluate]; rw [←integral_conj (𝕜:=ℂ), ← integral_const_mul]
          exact integral_congr_ae (Eventually.of_forall fun x=> by simp only [dual,Prod.swap_prod_mk,map_mul, starRingEnd_apply, star_star, t]; ac_rfl))
    _ = _ := (integral_integral_swap hi).symm.trans <| integral_congr_ae ((ofKernel_apply μ h g).mono fun x hx=> by
      dsimp only
      rw [RCLike.inner_apply,hx]; dsimp only [evaluate]; rw [← integral_mul_const]
      exact integral_congr_ae (Eventually.of_forall fun y=> by dsimp only [t]; rw [starRingEnd_apply]; ac_rfl))

private lemma trace_eq (h : Envelope U) (g : Envelope V) : trace μ U V = ∫ x, ⟪sec μ g x,sec μ (envDual h) x⟫ ∂μ := by
  -- trace written as ∫ t_y. Parseval applied in that direction.
  unfold trace; rw [integral_prod_symm]; swap
  · exact Env.integrableX (env_mult h (Env.along g measurable_swap)) _
  refine integral_congr_ae (Eventually.of_forall fun x=> ?_); dsimp only; rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memsec μ g x).coeFn_toLp,(memsec μ (envDual h) x).coeFn_toLp] with w s t
  rw [RCLike.inner_apply,sec,sec,s,t]; simp [dual]
omit [IsFiniteMeasure μ] in
private lemma partial_bound {ι : Type*} (b : HilbertBasis ι ℂ (Hilb μ)) (s : Finset ι) (x y : Hilb μ) :
    ‖∑ i∈s, ⟪x,b i⟫*⟪b i,y⟫‖ ≤ ‖x‖^2 + ‖y‖^2 := calc
  _ ≤ _ := norm_sum_le ..
  _ ≤ ∑ i∈s, (‖⟪b i,x⟫‖^2+‖⟪b i,y⟫‖^2) := sum_le_sum fun i _ => by
    rw [norm_mul,←inner_conj_symm x (b i),starRingEnd_apply,norm_star]; nlinarith [sq_nonneg (‖⟪b i,x⟫‖-‖⟪b i,y⟫‖)]
  _ ≤ _ := by rw [sum_add_distrib]; exact add_le_add (b.orthonormal.sum_inner_products_le ..) (b.orthonormal.sum_inner_products_le ..)
omit [IsFiniteMeasure μ] in
private lemma count_basis {ι : Type*} (b : HilbertBasis ι ℂ (Hilb μ)) [SecondCountableTopology (Hilb μ)] : Countable ι := by
  let s (i:ι) := Metric.ball (b i) (1/2)
  refine Pairwise.countable_of_isOpen_disjoint (s:=s) (fun i j h=> Metric.ball_disjoint_ball ?_) (fun _=> Metric.isOpen_ball) (fun _=> Metric.nonempty_ball.mpr (by norm_num))
  rw [dist_eq_norm]; have v:= norm_sub_sq (𝕜:=ℂ) (b i) (b j)
  rw [b.orthonormal.norm_eq_one,b.orthonormal.norm_eq_one,b.orthonormal.2 h,map_zero] at v
  nlinarith [norm_nonneg (b i-b j)]

theorem traceBasis [SecondCountableTopology (Hilb μ)] (h : Envelope U) (g : Envelope V) {ι : Type*} (b : HilbertBasis ι ℂ (Hilb μ)) :
    HasSum (fun i=> ⟪b i, ofKernel μ h (ofKernel μ g (b i))⟫) (trace μ U V) := by
  let T:=ofKernel μ h; let W:=ofKernel μ g; let H:=envDual h
  let F (i:ι) (x:X) := ⟪sec μ g x,b i⟫ * ⟪b i,sec μ H x⟫
  have ht (i : ι) : ∀ᵐ x ∂μ, F i x= ⟪(ofKernel μ H (b i)) x, W (b i) x⟫ := by
    filter_upwards [ofKernel_apply μ g (b i), ofKernel_apply μ H (b i)] with x z w
    unfold W; rw [w,z,evalInner μ g,evalInner μ H,RCLike.inner_apply,inner_conj_symm]
  have hF (i : ι) : Integrable (F i) μ := (integrable_congr (ht i)).mpr (L2.integrable_inner (ofKernel μ H (b i)) (W (b i)))
  have hv (i : ι) : ⟪b i, T (W (b i))⟫= ∫ x, F i x ∂μ := by
    rw [←ContinuousLinearMap.adjoint_inner_left]; unfold T; rw [← hilbertAdjoint]; exact (L2.inner_def _ _).trans (integral_congr_ae (EventuallyEq.symm (ht i)))
  let C := (factorM μ * cap g)^2+(factorM μ * cap H)^2
  haveI := count_basis μ b
  change Tendsto (fun s:Finset ι=> ∑ i∈s, ⟪b i,T (W (b i))⟫) atTop (𝓝 (trace μ U V))
  simp_rw [hv, ←integral_finsetSum _ (fun i _=> hF i)]
  rw [trace_eq μ h g]; refine tendsto_integral_filter_of_dominated_convergence (fun _=> C)
         (Eventually.of_forall fun s=> (integrable_finsetSum _ fun i _=> hF i).1) (Eventually.of_forall ?_) (integrable_const _) (Eventually.of_forall fun x=> b.hasSum_inner_mul_inner _ _)
  intro s; refine Eventually.of_forall fun x=> ?_
  exact (partial_bound μ b s _ _).trans (add_le_add (pow_le_pow_left₀ (norm_nonneg _) (sec_bound μ g x) _) (pow_le_pow_left₀ (norm_nonneg _) (sec_bound μ H x) _))
end YM.CF.Buffered.HS
#print axioms YM.CF.Buffered.HS.traceBasis

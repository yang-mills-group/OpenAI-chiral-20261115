import YM.SU5.Reconstruction.LinkMeasures.FrameTest
set_option autoImplicit false
set_option synthInstance.maxSize 12000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.PaymentCamera
open Function Filter Metric NormedSpace MeasureTheory Set
open scoped Topology ENNReal NNReal InnerProductSpace Classical
variable {X E:Type*}[MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (μ:Measure X)[IsFiniteMeasure μ](T: Test X→ₗ[ℂ]E)
/-- true compact local test with L1 cost, even at the top norm of the output test functions -/
noncomputable def imageBalls := closure (T '' {f| bill μ f≤ 1})
abbrev Frozen := IsCompact (imageBalls μ T)
@[simp] lemma imageBalls_zero:(0:E)∈ imageBalls μ T:= subset_closure ⟨0, by simp, T.map_zero⟩
lemma atBall(x:Test X)(p:bill μ x≤1):T x ∈ imageBalls μ T:=subset_closure ⟨x,p,rfl⟩
abbrev Affordable := ∃ C:ℝ, ∀ x, ‖T x‖≤ C*bill μ x
-- unit-scale estimate homogeneous, also for the seminorm case
lemma on_billing (C:ℝ)(p:∀ x,bill μ x ≤1→‖T x‖ ≤ C)(x:Test X) : ‖T x‖ ≤ C*bill μ x:= by
 rcases (bill_nonneg μ x).eq_or_lt with e | e
 · by_contra! he; rw [←e,mul_zero] at he; set z:= (max C 0+1)/‖T x‖; have ht:0<z:=by unfold z; positivity
   have h:= p ((z:ℂ) • x) (by rw [bill_scale,←e,mul_zero]; norm_num); rw [map_smul, norm_smul, Complex.norm_real,Real.norm_of_nonneg ht.le,show z*‖T x‖= max C 0+1 from div_mul_cancel₀ _ he.ne'] at h; grind
 · set z:= bill μ x; have h: ‖T ((z:ℂ)⁻¹ • x)‖ ≤ C:= p _ (by simp only [bill_scale,norm_inv,Complex.norm_real, Real.norm_of_nonneg (show 0≤z from e.le)]; change z⁻¹*z≤ _; exact (inv_mul_cancel₀ (show z≠0 from e.ne')).le); rw [map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (show 0≤z from e.le),mul_comm, ← div_eq_mul_inv, div_le_iff₀ (show 0<z from e)] at h; exact h
lemma offers_funds (p:Frozen μ T):Affordable μ T:=by
 obtain ⟨C,h⟩:= (p.image (continuous_norm (E:=E))).bddAbove; exact ⟨C,on_billing μ T C fun x v=> h ⟨T x, atBall μ T x v,rfl⟩⟩

-- square-plan for scalar probes, $T` on actual super-Ward programs not presuming meas in fine metric
variable (L:E→L[ℂ]ℂ)
noncomputable def board := L.toLinearMap.comp T
noncomputable def lector : Lp ℂ 2 μ := (InnerProductSpace.toDual ℂ _).symm ((board T L).extendOfNorm (seat μ 2))
noncomputable def hymn(x:X):ℂ := star ((lector μ T L) x)
lemma hail:Measurable (hymn μ T L) := (continuous_star.measurable).comp (Lp.stronglyMeasurable _).measurable
lemma hail_fin : Integrable (hymn μ T L) μ:= Complex.conjCLE.toContinuousLinearMap.integrable_comp ((Lp.memLp (lector μ T L)).integrable (by norm_num))
lemma tune (p:Frozen μ T)(x:Test X) : ∫ a, x.val a * hymn μ T L a∂μ=L (T x):=by
 obtain ⟨C,v⟩:=offers_funds μ T p
 have ht: ∃ C':ℝ,∀ i, ‖board T L i‖ ≤ C' * ‖seat μ 2 i‖:=by
   refine ⟨‖L‖ * max 0 C * squareCap μ, fun i=>?_⟩
   change ‖L (T i)‖ ≤ _
   rw [mul_assoc (‖L‖*_)]; rw [mul_assoc ‖L‖]; refine (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)); exact (v i).trans ((mul_le_mul_of_nonneg_right (le_max_right ..) (bill_nonneg ..)).trans (mul_le_mul_of_nonneg_left (cap_square ..) (le_max_left ..)))
 change _ = board T L x; rw [←LinearMap.extendOfNorm_eq (seats_supply μ 2 (by simp)) ht,←InnerProductSpace.toDual_symm_apply,L2.inner_def]; apply integral_congr_ae
 filter_upwards [(x.cost μ 2).coeFn_toLp] with a ha; change (seat μ 2 x) a = x.val a at ha; rw [ha]; rfl
lemma tune_set (p:Frozen μ T){A:Set X}(h:MeasurableSet A) : ∫ a in A,hymn μ T L a ∂μ=L (T (sample h 1)):=by
 rw [←tune μ T L p,←integral_indicator h]; apply integral_congr_ae (Eventually.of_forall fun i=>?_); change _=A.indicator (fun _=> (1:ℂ)) i*_; by_cases p:i∈A <;> simp [*]

end YM.PaymentCamera
#print axioms YM.PaymentCamera.tune

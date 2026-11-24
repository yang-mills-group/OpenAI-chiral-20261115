import YM.SU5.Reconstruction.LinkMeasures.Spirit
set_option autoImplicit false
set_option synthInstance.maxSize 12000
set_option maxHeartbeats 800000
noncomputable section
namespace YM.PaymentCamera
open Function Filter Metric NormedSpace MeasureTheory Set TopologicalSpace
open scoped Topology ENNReal NNReal InnerProductSpace Classical
variable {X E:Type*}[MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (μ:Measure X)[IsFiniteMeasure μ](T: Test X→ₗ[ℂ]E)(p:Frozen μ T)
variable (L:ℕ→ E→L[ℂ]ℂ)(q:InjOn (fun x i=>L i x) (sky (imageBalls μ T) : Set E))
local notation "K★" => imageBalls μ T
local notation "U★" => color μ T L
local notation "H★" => crop μ T L
private lemma upper_point (x:X)(h:H★ x∈ range (color μ T L)):∃ v:K★, color μ T L v=crop μ T L x:=h
private noncomputable def baseStone : K★:=⟨0,imageBalls_zero μ T⟩
private noncomputable def prism(x:X):K★:= if h:H★ x∈ range U★ then (upper_point μ T L x h).choose else baseStone μ T
include p
lemma prism_upper : ∀ᵐ x∂μ, color μ T L (prism μ T L x)=crop μ T L x:= by
 let ν:= μ.map (crop μ T L)
 have he:∀ᵐ x∂μ,crop μ T L x∈ν.support:= (ae_map_iff (crop_m μ T L).aemeasurable (@Measure.isClosed_support _ _ _ ν).measurableSet).mp (by exact ν.support_mem_ae)
 filter_upwards [he] with x hx
 rw [prism,dif_pos (crop_supported μ T p L _ hx)]; exact (upper_point μ T L x (crop_supported μ T p L _ hx)).choose_spec
include q
lemma prism_sched : StronglyMeasurable (prism μ T L):=by
 letI : MeasurableSpace E:= borel E; letI : BorelSpace E:=⟨rfl⟩
 haveI:CompactSpace (K★):= isCompact_iff_compactSpace.mp p
 have ht:Topology.IsClosedEmbedding (color μ T L):=(color_c ..).isClosedEmbedding (fun _ _ h=> Subtype.ext (q (sky_in _ (Subtype.mem _)) (sky_in _ (Subtype.mem _)) h))
 have he: U★ ∘ prism μ T L = fun x:X=> if crop μ T L x∈ range U★ then H★ x else color μ T L (baseStone μ T):=by
   funext x; by_cases h:H★ x∈ range U★; · simp only [comp_apply,prism,dif_pos h, if_pos h]; exact (upper_point μ T L x h).choose_spec
   simp only [comp_apply,prism,dif_neg h,if_neg h]
 have v:Measurable (prism μ T L):=ht.measurableEmbedding.measurable_comp_iff.mp (he ▸ Measurable.ite ((crop_m μ T L) ht.isClosed_range.measurableSet) (crop_m ..) measurable_const)
 exact v.stronglyMeasurable
omit q
lemma rise_bound (x:imageBalls μ T): x.val ∈ sky (imageBalls μ T):= sky_in _ x.property
lemma up_range (x:Test X): T x∈ sky (imageBalls μ T):= by
 set a:= 1+bill μ x
 have h':bill μ x < a:=by unfold a; linarith [bill_nonneg μ x]
 have ha:0<a:=(bill_nonneg ..).trans_lt h'
 have h:T ((a:ℂ)⁻¹ • x)∈ sky (imageBalls μ T):=sky_in _ (atBall μ T _ (by rw [bill_scale,norm_inv, Complex.norm_real,Real.norm_of_nonneg ha.le]; exact (mul_le_mul_of_nonneg_left h'.le (inv_nonneg.mpr ha.le)).trans_eq (inv_mul_cancel₀ ha.ne')))
 rw [map_smul] at h; have hv:= (sky (imageBalls μ T)).smul_mem (a:ℂ) h; rwa [smul_inv_smul₀ (by norm_cast; exact ha.ne')] at hv
-- note second countability of E *not* assumed.
variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]
omit p in
lemma sky_integral {f:X→E}{M: Submodule ℂ E}(P:IsClosed (M:Set E))(h:Integrable f μ)(u:∀ᵐ x∂μ,f x∈M): (∫ a, f a∂μ)∈ M:=by
 by_cases t:μ=0; · simp [t]
 haveI: NeZero μ:=⟨t⟩
 let N:= M.restrictScalars ℝ; rw [←integral_average μ f, integral_const]; exact N.smul_mem _ (N.convex.average_mem P u h)
include q
-- true representability at the operator cost, Bochner in sup topology target
structure CompactMarks (f:X→E):Prop where
 billed:StronglyMeasurable f
 opCompact:IsCompact (closure (range f))
omit p q
lemma CompactMarks.ration {f:X→E}(h:CompactMarks f):∃ C:ℝ,∀x,‖f x‖≤C:= by
 obtain ⟨C,p⟩:=(h.opCompact.image (continuous_norm (E:=E))).bddAbove; exact ⟨C,fun x=> p ⟨f x,subset_closure (mem_range_self _),rfl⟩⟩
lemma CompactMarks.all {f:X→E}(h:CompactMarks f):Integrable f μ:=by
 obtain ⟨C,v⟩:=h.ration; exact Integrable.of_bound h.billed.aestronglyMeasurable C (Eventually.of_forall v)
lemma CompactMarks.ticket {f:X→E}(h:CompactMarks f)(x:Test X):Integrable (fun i=> x.val i • f i) μ:=by
 obtain ⟨C,v⟩:= h.ration; refine Integrable.mono' ((x.finances μ).norm.mul_const C) (x.meas.aestronglyMeasurable.smul h.billed.aestronglyMeasurable) (Eventually.of_forall fun i=>?_); rw [norm_smul]; exact mul_le_mul_of_nonneg_left (v i) (norm_nonneg _)
include p q
lemma translator(x:Test X) : (∫ a, x.val a • (prism μ T L a).val∂μ)=T x:=by
 let f(a):E:= (prism μ T L a).val
 let g(a):E:= x.val a • f a
 have h0:CompactMarks f:=⟨continuous_subtype_val.comp_stronglyMeasurable (prism_sched μ T p L q),p.closure_of_subset (by rintro _ ⟨a,rfl⟩; exact Subtype.mem _)⟩
 have ht:Integrable g μ:=h0.ticket μ x
 change (∫ a,g a∂μ)=T x; refine q (sky_integral μ ((Submodule.span ℂ _).isClosed_topologicalClosure) ht (Eventually.of_forall fun a=> (sky (imageBalls μ T)).smul_mem _ (rise_bound μ T p _))) (up_range μ T p x) (funext fun i=>?_)
 change L i (∫ a,g a∂μ) = L i _; rw [←ContinuousLinearMap.integral_comp_comm (L i) ht,←tune μ T (L i) p]; apply integral_congr_ae
 filter_upwards [prism_upper μ T p L] with a ha
 unfold g; rw [map_smul]; exact congrArg (x.val a*·) (congrFun ha i)

structure Present (k:X→E):Prop where
 sensors:CompactMarks k
 receives(x:Test X): (∫ a,x.val a • k a ∂μ)=T x
omit L q
theorem buy_kernel:∃ k:X→E, Present μ T k ∧ ∀ a,k a∈ imageBalls μ T:=by
 obtain ⟨L,h⟩:= spi _ p
 let k(a:X):E:=(prism μ T L a).val
 have hk(a):k a∈imageBalls μ T:= (prism μ T L a).property
 refine ⟨k,⟨⟨continuous_subtype_val.comp_stronglyMeasurable (prism_sched μ T p L h),p.closure_of_subset (by rintro _ ⟨a,rfl⟩; exact hk a)⟩,translator μ T p L h⟩,hk⟩
end YM.PaymentCamera
#print axioms YM.PaymentCamera.buy_kernel
#print axioms YM.PaymentCamera.CompactMarks.ticket

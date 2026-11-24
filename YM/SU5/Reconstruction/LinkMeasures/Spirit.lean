import YM.SU5.Reconstruction.LinkMeasures.UnityVote
set_option autoImplicit false
set_option synthInstance.maxSize 12000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.PaymentCamera
open Function Filter Metric NormedSpace MeasureTheory Set TopologicalSpace
open scoped Topology ENNReal NNReal InnerProductSpace Classical
variable {X E:Type*}[MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]
/-! # Scalar support gluing -/
variable (μ:Measure X)[IsFiniteMeasure μ](T: Test X→ₗ[ℂ]E)(p:Frozen μ T)
noncomputable def sky (A:Set E): Submodule ℂ E:= (Submodule.span ℂ A).topologicalClosure
lemma sky_in (A:Set E): A ⊆ (sky A : Set E):= Submodule.subset_span.trans subset_closure
lemma spi (A:Set E)(p:IsCompact A): ∃ L:ℕ→E→L[ℂ]ℂ, InjOn (fun x i=> L i x) (sky A : Set E):=by
 let K:= sky A
 have ht:IsSeparable (K : Set E):= p.isSeparable.span.closure; haveI: SeparableSpace K:= ht.separableSpace
 let x:=denseSeq (↑K:Type _) ; choose L u v using fun i:ℕ=> exists_dual_vector'' ℂ (x i).val
 have he(z:E)(t:z∈K)(h:∀ i,L i z=0) : z=0:=by
   by_contra n
   have hp: 0<‖z‖:= norm_pos_iff.mpr n; set ε:=‖z‖/3; have e:0<ε:=by unfold ε; positivity
   obtain ⟨i,hi⟩:= Metric.denseRange_iff.mp (denseRange_denseSeq (↑K:Type _)) (⟨z,t⟩:K) ε e
   have a: dist (x i).val z< ε:= by rw [dist_comm]; exact hi
   have hz:‖(x i).val‖ ≤ dist (x i).val z:=by
      rw [dist_eq_norm]; refine le_trans (le_of_eq (show ‖(x i).val‖=‖L i ((x i).val-z)‖ from ?_)) ((ContinuousLinearMap.le_opNorm ..).trans (mul_le_of_le_one_left (norm_nonneg _) (u _))); rw [map_sub, v,h,sub_zero]; simp
   have ha:= norm_sub_norm_le z (x i).val; rw [norm_sub_rev,←dist_eq_norm] at ha; unfold ε at *; linarith
 refine ⟨L, @fun x hx y hy h=> sub_eq_zero.mp (he (x-y) (K.sub_mem hx hy) (fun i=>?_))⟩; rw [map_sub]; exact sub_eq_zero.mpr (congrFun h i)

noncomputable def zoom (A:Set X) : ℂ := ((μ.real A)⁻¹:ℝ)
noncomputable def hire {A:Set X}(h:MeasurableSet A): Test X:= zoom μ A • sample h 1
lemma hire_cost {A:Set X}(h:MeasurableSet A)(p:0<μ A): bill μ (hire μ h)=1:=by
 have hp:0<μ.real A:=ENNReal.toReal_pos p.ne' (measure_ne_top μ A); rw [hire,bill_scale,bill_zone,zoom,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr hp.le),inv_mul_cancel₀ hp.ne']
lemma gap_avg {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V] {A:Set X}
     (p:0<μ A){f:X→V}{z:V}{ε:ℝ}(t:∀ i∈ A, dist (f i) z≤ ε)(h:Integrable f μ) : dist ((μ.real A)⁻¹ • ∫ i in A, f i∂μ) z≤ ε:=by
    let a:= μ.real A; have ha:0<a:=ENNReal.toReal_pos p.ne' (measure_ne_top μ A)
    have ht:(a)⁻¹ • (∫ i in A, f i∂μ) - z = a⁻¹ • ∫ i in A, (f i - z) ∂μ:=by rw [integral_sub h.integrableOn (integrable_const _),setIntegral_const,smul_sub]; change _ = _ - a⁻¹ • a • z; rw [inv_smul_smul₀ ha.ne']
    rw [dist_eq_norm]; change ‖a⁻¹ • _ - z‖ ≤ _; rw [ht,norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ha.le)]; refine (mul_le_mul_of_nonneg_left (norm_setIntegral_le_of_norm_le_const (C:=ε) (measure_lt_top μ A) fun i u=> ?_) (inv_nonneg.mpr ha.le)).trans_eq ?_; · exact (dist_eq_norm (f i) z ▸ t i u: ‖f i-z‖≤ ε)
    change a⁻¹ * (ε*a)=_; field_simp

variable (L:ℕ→ E→L[ℂ]ℂ)
local notation "K★" => imageBalls μ T
noncomputable def color (e: imageBalls μ T) (i:ℕ):ℂ := L i e.val
@[fun_prop] lemma color_c : Continuous (color μ T L):= continuous_pi fun i=>(L i).continuous.comp continuous_subtype_val
noncomputable def crop(x:X) (i:ℕ):ℂ:=hymn μ T (L i) x
lemma crop_m:Measurable (crop μ T L):= measurable_pi_lambda _ fun i=> hail ..
noncomputable def wants(n:ℕ)(x:ℕ→ℂ)(ε:ℝ): Set (ℕ→ℂ):={u|∀ i∈ Finset.range n, dist (u i) (x i)< ε}
noncomputable def paysSet(n:ℕ)(x:ℕ→ℂ)(ε:ℝ):Set X:= crop μ T L ⁻¹' (wants n x ε)
lemma wants_open (n x ε): IsOpen (wants n x ε):=by
 rw [show wants n x ε=⋂ i ∈ Finset.range n, (fun x:ℕ→ℂ=> x i) ⁻¹' ball (x i) ε from by ext; simp [wants]]; apply isOpen_biInter_finset; exact fun i h=> isOpen_ball.preimage (continuous_apply i)
lemma paid_m (n x ε): MeasurableSet (paysSet μ T L n x ε):= (crop_m μ T L) (wants_open n x ε).measurableSet
lemma wants_payable (n x ε)(hx:x∈(μ.map (crop μ T L)).support)(e:0<ε): 0< μ (paysSet μ T L n x ε):= by
 rw [paysSet, ←Measure.map_apply (crop_m ..) (wants_open n x ε).measurableSet]; exact ((μ.map _).mem_support_iff_forall x).mp hx _ ((wants_open ..).mem_nhds (fun i _=> by rw [dist_self]; exact e))
include p
lemma at_point(x:ℕ→ℂ)(ε:ℝ)(hx:x∈(μ.map (crop μ T L)).support) (t:0<ε)(n i:ℕ)(e:i<n):dist (L i (T (hire μ (paid_m μ T L n x ε)))) (x i) ≤ ε:=by
 let f:=hymn μ T (L i)
 let A:= paysSet μ T L n x ε
 rw [hire, map_smul,map_smul,←tune_set μ T (L i) p,zoom,Complex.coe_smul]
 apply gap_avg μ (wants_payable μ T L n x ε hx t) _ (hail_fin ..)
 intro a u
 change ∀ j∈ Finset.range n, dist (crop μ T L a j) _ < ε at u
 exact (u i (Finset.mem_range.mpr e)).le
lemma crop_supported(x:ℕ→ℂ)(hx:x∈(μ.map (crop μ T L)).support) : x∈ Set.range (color μ T L):=by
 let ε(n:ℕ):ℝ:= 1 /((n:ℝ)+1); have hp (n):0<ε n:=by unfold ε; positivity
 let X'(n:ℕ):K★:= ⟨T (hire μ (paid_m μ T L n x (ε n))), atBall μ T _ (hire_cost μ _ (wants_payable μ T L n x (ε n) hx (hp n))|>.le)⟩
 haveI : CompactSpace (K★):= isCompact_iff_compactSpace.mp p
 refine (isCompact_range (color_c μ T L)).isClosed.mem_of_tendsto (b:=atTop) (f:=fun i=> color μ T L (X' i)) ?_ (Eventually.of_forall fun _=> mem_range_self _)
 refine tendsto_pi_nhds.mpr fun i=> Metric.tendsto_nhds.mpr fun δ h=> ?_
 have ht: Tendsto ε atTop (𝓝 0):=tendsto_one_div_add_atTop_nhds_zero_nat
 filter_upwards [ht.eventually (gt_mem_nhds h),eventually_gt_atTop i] with n h' e
 let f:= hymn μ T (L i)
 let A:= paysSet μ T L n x (ε n)
 exact (at_point μ T p L x (ε n) hx (hp n) n i e).trans_lt (show ε n<δ from h')
end YM.PaymentCamera
#print axioms YM.PaymentCamera.crop_supported
#print axioms YM.PaymentCamera.spi

import YM.SU5.Reconstruction.LinkMeasures.CastUp
set_option autoImplicit false
set_option synthInstance.maxSize 12000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.PaymentCamera
open Function Filter Metric NormedSpace MeasureTheory Set TopologicalSpace
open scoped Topology ENNReal NNReal InnerProductSpace Classical
variable {X E:Type*}[MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (μ:Measure X)[IsFiniteMeasure μ](T: Test X→ₗ[ℂ]E){k: X→E}{S :Set E}
noncomputable def frequents (k:X→E):Set E:= {e| ∀ ε>0, 0 < μ (k ⁻¹' ball e ε)}
lemma center_hold (p:CompactMarks k):∀ᵐ x∂μ,k x∈ frequents μ k := by
 let K:=closure (range k); let r(x:X):K:=⟨k x,subset_closure (mem_range_self _)⟩
 letI: MeasurableSpace E:=borel E; letI:BorelSpace E:=⟨rfl⟩
 haveI:CompactSpace K:=isCompact_iff_compactSpace.mp p.opCompact
 have v:Measurable r:=p.billed.measurable.subtype_mk
 let ν:=μ.map r; have t:∀ᵐ x∂μ,r x∈ν.support:=(ae_map_iff v.aemeasurable (@Measure.isClosed_support _ _ _ ν).measurableSet).mp ν.support_mem_ae
 filter_upwards [t] with x hx ε h
 have ht:= (ν.mem_support_iff_forall _).mp hx _ (ball_mem_nhds (r x) h); unfold ν at ht; rw [Measure.map_apply v measurableSet_ball] at ht; exact ht
variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]
lemma Present.from_patch (p:Present μ T k){A:Set X}(h:MeasurableSet A): T (sample h 1)=∫ a in A,k a∂μ:=by rw [←p.receives,←integral_indicator h]; apply integral_congr_ae; apply Eventually.of_forall; intro x; change A.indicator (fun _=> (1:ℂ)) x • _ = _; by_cases e:x∈A <;> simp only [indicator_of_mem,indicator_of_notMem,e,not_false_eq_true,one_smul,zero_smul]
lemma Present.point_cost (p:Present μ T k)(e:E)(t:e∈ frequents μ k): e ∈ imageBalls μ T:=by
 refine Metric.mem_closure_iff.mpr fun ε v=>?_; let a:=ε/2; have hp:0<a:=half_pos v; let A:= k ⁻¹' ball e a; letI : MeasurableSpace E := borel E; letI : BorelSpace E:=⟨rfl⟩; have hm:MeasurableSet A:=p.sensors.billed.measurable measurableSet_ball
 have h:0<μ A:=t a hp; refine ⟨T (hire μ hm),⟨hire μ hm,(hire_cost μ hm h).le,rfl⟩,?_⟩; rw [hire,map_smul,p.from_patch μ T hm,zoom, show (((μ.real A)⁻¹:ℝ):ℂ)=(algebraMap ℝ ℂ) ((μ.real A)⁻¹) from rfl,algebraMap_smul,dist_comm]; exact (gap_avg μ h (fun i m=>m.le) (p.sensors.all μ)).trans_lt (half_lt_self v)
lemma Present.from_span {M:Submodule ℂ E} (p:Present μ T k)(h:IsClosed (M:Set E))(u: frequents μ k⊆ (M:Set E))(x:Test X) : T x∈ M:= by rw [←p.receives]; exact sky_integral μ h (p.sensors.ticket μ x) ((center_hold μ p.sensors).mono fun i e=> M.smul_mem _ (u e))
lemma present_sub {T U: Test X→ₗ[ℂ]E}{v:X→ E}(p:Present μ T k)(q:Present μ U v): Present μ (T-U) (k-v):=by
 have h: Set.range (k-v)⊆ (fun z:E×E=> z.1-z.2) '' ((closure (range k)) ×ˢ (closure (range v))):=by rintro _ ⟨a,rfl⟩; exact ⟨(k a,v a),⟨subset_closure (mem_range_self _),subset_closure (mem_range_self _)⟩,rfl⟩
 refine ⟨⟨p.sensors.billed.sub q.sensors.billed, ((p.sensors.opCompact.prod q.sensors.opCompact).image (continuous_fst.sub continuous_snd)).closure_of_subset h⟩,fun x=>?_⟩; change (∫ i, x.val i • (k i-v i)∂μ)=_; simp_rw [smul_sub, LinearMap.sub_apply]; rw [integral_sub (p.sensors.ticket μ x) (q.sensors.ticket μ x),p.receives,q.receives] -- tune
lemma point_budget (p:Present μ T k)(C:ℝ)(h:∀ (x:Test X), bill μ x≤1→‖T x‖ ≤ C):∀ᵐ i∂μ, ‖k i‖ ≤ C:=by
 filter_upwards [center_hold μ p.sensors] with i t
 have h':imageBalls μ T ⊆ {x|‖x‖≤C}:= by refine closure_minimal ?_ (isClosed_le continuous_norm continuous_const); rintro y ⟨x,hx,rfl⟩; exact h x hx
 exact h' (p.point_cost μ T _ t)
lemma point_control {T U: Test X →ₗ[ℂ]E}{v:X→ E}(p:Present μ T k)(q:Present μ U v)(ε:ℝ)(h:∀ x, bill μ x≤1→dist (T x) (U x) ≤ ε): ∀ᵐ i∂μ, dist (k i) (v i) ≤ ε:= by
 have hp:= point_budget μ _ (present_sub μ p q) ε (fun x v=> (dist_eq_norm (T x) _ ▸ h x v))
 simp_rw [dist_eq_norm]; exact hp
end YM.PaymentCamera
#print axioms YM.PaymentCamera.point_control
#print axioms YM.PaymentCamera.Present.from_span

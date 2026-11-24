import YM.SU5.Reconstruction.LinkMeasures.PointReads
set_option autoImplicit false
set_option synthInstance.maxSize 12000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.PaymentCamera
open Function Filter Metric NormedSpace MeasureTheory Set TopologicalSpace
open scoped Topology ENNReal NNReal InnerProductSpace Classical
variable {X E:Type*}[MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (μ:Measure X)[IsFiniteMeasure μ](F: Test X→ₗ[ℂ]E)(R: ℕ→ Test X→ₗ[ℂ]E)[CompleteSpace E]
lemma rounded (h:∀ e>0,∃ W:Finset (Test X),∀ x,bill μ x≤ 1→∃ a∈W,dist (F x) (F a) ≤ e): Frozen μ F:=by
 apply TotallyBounded.isCompact_of_isComplete _ isClosed_closure.isComplete; apply TotallyBounded.closure; refine Metric.totallyBounded_iff.mpr fun ε e=> ?_
 obtain ⟨W,h⟩:=h _ (half_pos e); let A:= (W.image (fun i=>F i): Finset E); refine ⟨(A:Set E), A.finite_toSet, ?_⟩; rintro _ ⟨x,hx,rfl⟩; obtain ⟨a,t,h⟩:= h x hx; exact Set.mem_iUnion.mpr ⟨F a, Set.mem_iUnion.mpr ⟨Finset.mem_image_of_mem _ t,h.trans_lt (half_lt_self e)⟩⟩

structure Council : Prop where
 tables (e:ℝ):0<e →∃ W:Finset (Test X), ∀ᶠ r:ℕ in atTop,∀ x,bill μ x≤1 →∃ a∈W,∀ i,r ≤ i→dist (R i x) (R i a)≤e
 limit (x:Test X): Tendsto (fun i=>R i x) atTop (𝓝 (F x))
 pensions: ∀ᶠ i:ℕ in atTop,Frozen μ (R i)

lemma Council.reservation (p:Council μ F R):Frozen μ F:=by
 refine rounded μ F fun e h=> ?_; obtain ⟨W,t⟩:= p.tables _ h; obtain ⟨r,t⟩:= t.exists; refine ⟨W,fun x v=>?_⟩; obtain ⟨a,v,h⟩:=t x v; exact ⟨a,v,le_of_tendsto ((p.limit x).dist (p.limit a)) ((eventually_ge_atTop r).mono h)⟩ -- Monotone argument? h is fun i..
lemma Council.commands (p:Council μ F R)(ε:ℝ)(h:0<ε): ∀ᶠ i:ℕ in atTop,∀ x,dist (R i x) (F x)≤ε * bill μ x:=by
 let d:= ε/3
 have hd:0<d:=by unfold d; positivity
 obtain ⟨W,t⟩:= p.tables _ hd; obtain ⟨r,t⟩:= t.exists
 have he: ∀ᶠ i:ℕ in atTop, ∀ a∈W,dist (R i a) (F a)≤d:= (eventually_all_finset W).mpr fun a _=> (Metric.tendsto_nhds.mp (p.limit a) d hd).mono fun _ p=> p.le
 filter_upwards [he, eventually_ge_atTop r] with i P h'
 simp_rw [dist_eq_norm]
 apply on_billing μ (R i-F) ε
 intro x hx
 change ‖R i x-F x‖ ≤ ε; rw [←dist_eq_norm]
 obtain ⟨a,v,p'⟩:= t x hx; have he: dist (F x) (F a) ≤ d:=le_of_tendsto ((p.limit x).dist (p.limit a)) ((eventually_ge_atTop r).mono fun i h=> p' i h)
 have hx:=P a v; have hv:=p' i h'; unfold d at *; linarith [dist_triangle (R i x) (R i a) (F a),dist_triangle_right (R i x) (F x) (F a)]
-- compact densities even before limit, and actual norm comparison per-input point
variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
structure Grants (k:X→E):Prop where
 publicly : Present μ F k
 along : ∃ D:ℕ→ X→ E,(∀ᶠ i:ℕ in atTop, Present μ (R i) (D i)) ∧ ∀ ε>0,∀ᶠ i:ℕ in atTop,∀ᵐ x∂μ,dist (D i x) (k x)≤ ε
 warm (ε:ℝ):0< ε→∀ᶠ i:ℕ in atTop,∀ x,dist (R i x) (F x)≤ε * bill μ x

lemma grants (p:Council μ F R):∃ k:X→ E, Grants μ F R k ∧ ∀ x,k x∈ imageBalls μ F:=by
 obtain ⟨k,h,v⟩:=buy_kernel μ F (p.reservation μ F R)
 let D (i:ℕ): X→ E:= if p:Frozen μ (R i) then (buy_kernel μ (R i) p).choose else 0; have tp:∀ᶠ i:ℕ in atTop, Present μ (R i) (D i):= p.pensions.mono fun i p=> by rw [show D i= _ from dif_pos p]; exact (buy_kernel μ (R i) p).choose_spec.1
 refine ⟨k, ⟨h,⟨D,tp,fun ε w=>?_⟩, p.commands μ F R⟩,v⟩; filter_upwards [tp,p.commands μ F R ε w] with i u w'
 exact point_control μ u h _ fun i t=> (w' i).trans (mul_le_of_le_one_right w.le t)
end YM.PaymentCamera
#print axioms YM.PaymentCamera.grants

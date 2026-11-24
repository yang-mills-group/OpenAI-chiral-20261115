import GaugeFieldConstruction.PetalMars
/-!
# smooth expenditures through integrals, derivative visits
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom
open Function Set Filter MeasureTheory Measure Complex Analysis Points Bulb
open scoped ContDiff Topology BigOperators
variable {n:ℕ}
-- point qualifications
structure BreatherMars (b:Bulb)(k:Fin n)(x:Points n): Prop where
 bounds : x∈conf n
 home : b.lit (x k)
 apart : ∀ i,i≠k→ x i∉ b.run
variable (b:Bulb)(k:Fin n) (x : Points n) (h:BreatherMars b k x)
lemma BreathingMars : IsOpen {x : Points n | BreatherMars b k x}:=isOpen_iff_mem_nhds.mpr (fun x hx=> by change BreatherMars b k x at hx; filter_upwards [(conf_open _).mem_nhds hx.bounds, HoursMars x k b hx.home hx.apart] with i hi hv; exact ⟨hi,hv.1,hv.2⟩)
lemma BreatherSupportMars (U:Set (Points n))(w:∀ x∈U, BreatherMars b k x)(f:Test n)(p:tsupport f ⊆ U) : b.Works f k:=⟨fun x hx=>(w x (p hx)).home,fun x hx=>(w x (p hx)).apart⟩
include h
lemma RoomMars (y:E4)(hy:y∈b.shore):cons y x∈conf _:= first_conf _ h.bounds (by
 intro i v; change x i=y at v; rw [←v] at hy; by_cases p:i=k
 · subst k; exact centre h.home hy
 exact h.apart i p (strands hy))
omit h
-- general integration smooth calculus. via Supports prop
section Any
variable {G : Type*} [NormedAddCommGroup G][NormedSpace ℝ G][CompleteSpace G]
variable (F:E4 × Points n → G)(U:Set (Points n))(u:IsOpen U)(D:Set E4)(d:IsCompact D)
variable (H:∀ x∈U, ∀ y, ContDiffAt ℝ ∞ F (y,x))
variable (e:∀ x∈U, ∀ y,y∉D→F (y,x)=0) -- expect syntax spaces
noncomputable def WrapMars (F:E4×Points n→G) (x:Points n):G:=∫ y:E4,F (y,x)
noncomputable def CPderMars (F:E4×Points n→G) (p:E4×Points n):= fderiv ℝ F p ∘L ContinuousLinearMap.inr ℝ E4 (Points n)
lemma CPMars (x:Points n)(y:E4)(a:DifferentiableAt ℝ F (y,x)): HasFDerivAt (fun x=> F (y,x)) (CPderMars F (y,x)) x:= a.hasFDerivAt.comp x ((hasFDerivAt_const y x).prodMk (hasFDerivAt_id ..)) -- const order tune
include H u
lemma CPSmoothMars : ∀ x∈U,∀ y, ContDiffAt ℝ ∞ (CPderMars F) (y,x):= by
 have hx:IsOpen (univ ×ˢ U:Set (E4 × Points n)):=isOpen_univ.prod u -- tune
 intro x v y
 let T (y:E4×Points n):= fderiv ℝ F y
 have hF:ContDiffOn ℝ ∞ F (univ ×ˢ U):=fun p hp=> (H p.2 hp.2 p.1).contDiffWithinAt
 have hp:ContDiffOn ℝ ∞ T (univ ×ˢ U):=(hF.fderiv_of_isOpen hx (by simp))
 exact ((hp (y,x) (by simp[v])).contDiffAt (hx.mem_nhds (by simp[v]))).clm_comp contDiffAt_const
include e
lemma CPSellMars : ∀ x∈U,∀ y,y∉D→CPderMars F (y,x)=0:=by
 intro x hx y hy
 have he:(fun x=>F (y,x)) =ᶠ[𝓝 x] fun _=> (0:G):= Eventually.mono (u.mem_nhds hx) (fun i t=> e i t y hy)
 exact (CPMars F x y ((H _ hx y).differentiableAt (by simp))).unique ((hasFDerivAt_const (0:G) x).congr_of_eventuallyEq he) -- order
include d
omit u in
lemma CohortMars (x:Points n)(hx:x∈U) : Integrable (fun y:E4=>F (y,x)):= by
 have hv:Continuous (fun y:E4=>F (y,x)):= continuous_iff_continuousAt.mpr fun y=> (H x hx y).continuousAt.comp_of_eq (f:=fun y:E4=>(y,x)) (continuousAt_id.prodMk continuousAt_const) rfl
 exact hv.integrable_of_hasCompactSupport (d.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (fun i h=> not_not.mp fun v=> h (e x hx i v)) d.isClosed))
lemma inventoryMars (x:Points n)(hx:x∈U): HasFDerivAt (WrapMars F) (WrapMars (CPderMars F) x) x:=by
 classical
 obtain ⟨r,hr,he⟩:= Metric.nhds_basis_closedBall.mem_iff.mp (u.mem_nhds hx)
 let V:=Metric.closedBall x r
 let t:=CPderMars F
 have ht:= CPSmoothMars F U u H
 have hF:ContinuousOn (fun p=> ‖t p‖) (D×ˢ V):=fun p i=> ((ht p.2 (he i.2) p.1).continuousAt.norm).continuousWithinAt
 obtain ⟨C,hC⟩:= ((d.prod (isCompact_closedBall ..)).image_of_continuousOn hF).bddAbove
 let f:= D.indicator (fun _=> C)
 have hbound: Integrable f:= (integrableOn_const d.measure_lt_top.ne).integrable_indicator d.measurableSet -- tune
 refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s:=V) (Metric.closedBall_mem_nhds x hr) ?_ (CohortMars F U D d H e _ hx) (CohortMars _ _ _ d (CPSmoothMars F U u H) (CPSellMars F U u D H e) x hx).aestronglyMeasurable ?_ hbound (Eventually.of_forall (fun y q h=>CPMars F q y ((H _ (he h) y).differentiableAt (by simp))))
 · exact Eventually.mono (u.mem_nhds hx) fun i p=> (CohortMars F U D d H e i p).aestronglyMeasurable
 refine Eventually.of_forall fun y z hz=> ?_
 change ‖t (y,z)‖≤f y; by_cases g:y∈D
 · rw [show f y=C from indicator_of_mem g _]; exact hC ⟨(y,z),⟨g,hz⟩,rfl⟩
 rw[show f y=0 from indicator_of_notMem g _,show t (y,z)=0 from CPSellMars _ _ u _ H e _ (he hz) _ g,norm_zero]
lemma CubicDMars (x:Points n)(hx:x∈U) (v: Points n) : Analysis.D v (WrapMars F) x=∫ y:E4, Analysis.D (0,v) F (y,x) :=by
 let T :=CPderMars F
 have he: Integrable (fun y=> T (y,x)):= CohortMars T _ _ d (CPSmoothMars F U u H) (CPSellMars F U u D H e) x hx
 unfold Analysis.D; rw [(inventoryMars F U u D d H e _ hx).fderiv]; exact ((ContinuousLinearMap.apply ℝ G v).integral_comp_comm he).symm -- orientation
end Any
#print axioms inventoryMars
end YM.GaugeFieldConstruction.Fathom

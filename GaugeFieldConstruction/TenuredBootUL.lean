import GaugeFieldConstruction.TraceBootUL
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom
open Function Filter Analysis Points Set MeasureTheory Measure Complex
open scoped Topology BigOperators ContDiff Classical
variable {n:ℕ}
variable {G : Type*} [NormedAddCommGroup G][NormedSpace ℝ G][CompleteSpace G]
variable (F:E4 × Points n → G)(U:Set (Points n))(u:IsOpen U)(D:Set E4)(d:IsCompact D)(m:ℕ)
variable (H:∀ x∈U, ∀ y, ContDiffAt ℝ ((m+1:ℕ):WithTop ℕ∞) F (y,x))(e:∀ x∈U, ∀ y,y∉D→F (y,x)=0)
include H u
lemma CPSmUL : ∀ x∈U,∀ y, ContDiffAt ℝ m (CPderMars F) (y,x):= by
 have hx:IsOpen (univ ×ˢ U:Set (E4 × Points n)):=isOpen_univ.prod u
 intro x v y
 let T (y:E4×Points n):= fderiv ℝ F y
 have hF:ContDiffOn ℝ ((m+1:ℕ):WithTop ℕ∞) F (univ ×ˢ U):=fun p hp=> (H p.2 hp.2 p.1).contDiffWithinAt
 have hp:ContDiffOn ℝ m T (univ ×ˢ U):=(hF.fderiv_of_isOpen hx (by simp))
 exact ((hp (y,x) (by simp[v])).contDiffAt (hx.mem_nhds (by simp[v]))).clm_comp contDiffAt_const
include e
lemma CPselUL : ∀ x∈U,∀ y,y∉D→CPderMars F (y,x)=0:=by
 intro x hx y hy
 have he:(fun x=>F (y,x)) =ᶠ[𝓝 x] fun _=> (0:G):= Eventually.mono (u.mem_nhds hx) (fun i t=> e i t y hy)
 exact (CPMars F x y ((H _ hx y).differentiableAt (by simp))).unique ((hasFDerivAt_const (0:G) x).congr_of_eventuallyEq he)
include d
omit u H in
lemma cohortsUL (z:ℕ)(p:∀ x∈U,∀ y,ContDiffAt ℝ z F (y,x))(x:Points n)(hx:x∈U) : Integrable (fun y:E4=>F (y,x)):= by
 have hv:Continuous (fun y:E4=>F (y,x)):= continuous_iff_continuousAt.mpr fun y=> (p x hx y).continuousAt.comp_of_eq (f:=fun y:E4=>(y,x)) (continuousAt_id.prodMk continuousAt_const) rfl
 exact hv.integrable_of_hasCompactSupport (d.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (fun i h=> not_not.mp fun v=> h (e x hx i v)) d.isClosed))
lemma InvertUL (x:Points n)(hx:x∈U): HasFDerivAt (WrapMars F) (WrapMars (CPderMars F) x) x:=by
 classical
 obtain ⟨r,hr,he⟩:= Metric.nhds_basis_closedBall.mem_iff.mp (u.mem_nhds hx)
 let V:=Metric.closedBall x r
 let t:=CPderMars F
 have ht:= CPSmUL F U u m H
 have hF:ContinuousOn (fun p=> ‖t p‖) (D×ˢ V):=fun p i=> ((ht p.2 (he i.2) p.1).continuousAt.norm).continuousWithinAt
 obtain ⟨C,hC⟩:= ((d.prod (isCompact_closedBall ..)).image_of_continuousOn hF).bddAbove
 let f:= D.indicator (fun _=> C)
 have hbound: Integrable f:= (integrableOn_const d.measure_lt_top.ne).integrable_indicator d.measurableSet
 refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s:=V) (Metric.closedBall_mem_nhds x hr) ?_ (cohortsUL F U D d e (m+1) H _ hx) (cohortsUL _ _ _ d (CPselUL F U u D m H e) m ht x hx).aestronglyMeasurable ?_ hbound (Eventually.of_forall (fun y q h=>CPMars F q y ((H _ (he h) y).differentiableAt (by simp))))
 · exact Eventually.mono (u.mem_nhds hx) fun i p=> (cohortsUL F U D d e _ H i p).aestronglyMeasurable
 refine Eventually.of_forall fun y z hz=> ?_
 change ‖t (y,z)‖≤f y; by_cases g:y∈D
 · rw [show f y=C from indicator_of_mem g _]; exact hC ⟨(y,z),⟨g,hz⟩,rfl⟩
 rw[show f y=0 from indicator_of_notMem g _,show t (y,z)=0 from CPselUL _ _ u _ m H e _ (he hz) _ g,norm_zero]
omit H
lemma convolveUL (p:∀ x∈U, ∀ y,ContDiffAt ℝ m F (y,x)): ContDiffOn ℝ m (WrapMars F) U:=by
 induction m generalizing G with
 | zero =>
   have ht:ContinuousOn (WrapMars F) U:= continuousOn_integral_of_compact_support d (?_ : ContinuousOn (fun t:Points n × E4=> F (t.2,t.1)) (U ×ˢ univ)) (fun x y h v=>e _ h y v) -- requires specify
   · simpa using ht
   intro t h; exact ((p _ h.1 t.2).continuousAt.comp (f:=fun x:Points n × E4=>(x.2,x.1)) (continuous_snd.prodMk continuous_fst).continuousAt).continuousWithinAt
 | succ m ih =>
   have hp:=InvertUL F U u D d m p e
   rw [Nat.cast_add_one,contDiffOn_succ_iff_fderiv_of_isOpen u]
   exact ⟨fun x h=> (hp _ h).differentiableAt.differentiableWithinAt,by simp, (ih _ (CPselUL F U u D _ p e) (CPSmUL F U u _ p)).congr fun x hx=>(hp _ hx).fderiv⟩
#print axioms convolveUL
end YM.GaugeFieldConstruction.Fathom
end

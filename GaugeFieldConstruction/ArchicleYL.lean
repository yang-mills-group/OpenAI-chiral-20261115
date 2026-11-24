import GaugeFieldConstruction.LeitYL
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom
open Function Filter Analysis Points Set MeasureTheory Measure Complex
open scoped Topology BigOperators ContDiff Classical
variable {n:ℕ}(a:Axis)(p:Points n)(b:Bulb)(i:Axis)(k:Fin n)(r:ℝ)
abbrev VestHYL (b:Bulb)(a:Axis): Set E4:= (b.LED a).run
lemma vestKYL:IsCompact (VestHYL b a):= (b.LED a).c
noncomputable def landRentYL {X:Type*}[MeasureSpace X](K:Set X): Measure K:= Measure.comap ((↑): K→X) (volume:Measure X)
lemma rentalYL {X:Type*}[MeasureSpace X](K:Set X)(h:MeasurableSet K)(k:volume K < ⊤): IsFiniteMeasure (landRentYL K):=by
 refine ⟨?_⟩; rw[landRentYL,comap_subtype_coe_apply h]; simpa using k -- tune
lemma alphaFinYL: IsFiniteMeasure (landRentYL α0_YL):= rentalYL α0_YL isCompact_Icc.measurableSet isCompact_Icc.measure_lt_top
lemma vestFinYL : IsFiniteMeasure (landRentYL (VestHYL b a)):= rentalYL _ (vestKYL a b).measurableSet (vestKYL a b).measure_lt_top
noncomputable def raysCostYL (b:Bulb)(a:Axis)(T:Points (n+1) → ℂ)(p:Points n):= ∫ x:E4, D (basis a) b.f x • T (Points.cons x p)
noncomputable def DimYL (b:Bulb)(a:Axis)(x:E4):ℂ:= ((D (basis a) b.f x:ℝ):ℂ)
lemma beamInkYL: Continuous (DimYL b a):= Complex.continuous_ofReal.comp (b.LED a).d.continuous
lemma raysVisitYL (T:Points (n+1)→ℂ): raysCostYL b a T p=∫ x: VestHYL b a, DimYL b a x.val*T (Points.cons x.val p) ∂ landRentYL _ :=by
 let A:=VestHYL b a; let U(x:E4):=DimYL b a x*T (Points.cons x p)
 rw [show (∫ x:A, _∂landRentYL A)=∫ x:A,U x.val ∂landRentYL A from rfl,landRentYL,integral_subtype_comap (vestKYL a b).measurableSet]
 rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
 · exact integral_congr_ae (Eventually.of_forall fun x=> Complex.real_smul) -- tune
 intro x u; have h:D (basis a) b.f x=0:= image_eq_zero_of_notMem_tsupport u -- tune names
 simp [U,DimYL,h]
lemma rayαYL (T:ℝ→ℂ): (∫ x:α0_YL,T x.val ∂landRentYL α0_YL)=∫ x in (0:ℝ)..1,T x:=by rw [landRentYL,integral_subtype_comap measurableSet_Icc, integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le zero_le_one]
abbrev ZonesYL (b:Bulb)(a:Axis):= α0_YL × VestHYL b a -- expects set as Type? coeSort
noncomputable abbrev rayMoveYL (a:Axis)(p:Points n)(k:Fin n)(r:ℝ)(b:Bulb)(i:Axis)(x:ZonesYL b i):=Points.cons x.2.val (ledgeYL k a r p x.1.val)
noncomputable abbrev rayPenYL (b:Bulb)(i:Axis)(x: ZonesYL b i):= DimYL b i x.2.val
noncomputable abbrev rayonZYL (b:Bulb)(i:Axis): Measure (ZonesYL b i):= (landRentYL α0_YL).prod (landRentYL (VestHYL b i))
lemma RΦayComYL: CompactSpace (ZonesYL b i):=by haveI := isCompact_iff_compactSpace.mp (vestKYL i b); unfold ZonesYL; exact inferInstance
lemma RΦayCanYL: IsFiniteMeasure (rayonZYL b i):=by haveI:=alphaFinYL; haveI:=vestFinYL i b; unfold rayonZYL; exact inferInstance
lemma RΦayPriceYL : Continuous (rayPenYL b i):= (beamInkYL i b).comp (continuous_subtype_val.comp continuous_snd)
lemma alabasterYL : Continuous (fun p:E4×Points n=> Points.cons p.1 p.2):=by
 let A(x:E4 × Points n):= (Points.cons x.1 x.2).ofLp; apply (PiLp.continuous_toLp 2 _).comp (show Continuous A from continuous_pi ?_)
 intro i; refine Fin.cases ?_ ?_ i; exact continuous_fst; intro j; exact Continuous.comp (show Continuous (fun p:Points n=>p j) by fun_prop) continuous_snd
lemma RΦayMotionYL : Continuous (rayMoveYL a p k r b i):= alabasterYL.comp ((continuous_subtype_val.comp continuous_snd).prodMk ((ledgeSureYL a p k r).comp (continuous_subtype_val.comp continuous_fst)))
variable (h:calmYL k a r p b)
include h
lemma RΦayHappyYL (x: ZonesYL b i): rayMoveYL a p k r b i x∈ conf (n+1):= RoomMars _ _ _ (h x.1.val x.1.2) x.2.val (Bulb.cone b i x.2.2)
noncomputable def ScrollOpYL (a:Axis)(p:Points n)(b:Bulb)(i:Axis)(k:Fin n)(r:ℝ) (T:Points (n+1)→ℂ):=∫ x, rayPenYL b i x*T (rayMoveYL a p k r b i x)∂rayonZYL b i
lemma ScrollEarnYL (T:Points (n+1)→ ℂ)(v:ContinuousOn T (conf (n+1))): Integrable (fun x:ZonesYL b i=>rayPenYL b i x*T (rayMoveYL a p k r b i x)) (rayonZYL b i):=by
 haveI:=RΦayComYL b i; haveI:=RΦayCanYL b i
 have he : Continuous (fun x:ZonesYL b i=>T (rayMoveYL a p k r b i x)):= continuous_iff_continuousAt.mpr fun x=> (v.continuousAt ((conf_open _).mem_nhds (RΦayHappyYL a p b i k r h x))).comp (RΦayMotionYL a p b i k r).continuousAt
 exact ((RΦayPriceYL b i).mul he).integrable_of_hasCompactSupport (isClosed_tsupport .. |>.isCompact)
lemma ScrollCubicYL(T:Points (n+1)→ ℂ)(v:ContinuousOn T (conf (n+1))): ScrollOpYL a p b i k r T=∫ x:α0_YL, raysCostYL b i T (ledgeYL k a r p x.val)∂ landRentYL α0_YL:=by
 haveI:= vestFinYL i b; haveI:=alphaFinYL
 unfold ScrollOpYL; rw [integral_prod _ (ScrollEarnYL a p b i k r h T v)]; apply integral_congr_ae; refine Eventually.of_forall ?_; intro x; exact (raysVisitYL i (ledgeYL k a r p x.val) b T).symm
lemma RayCubeYL (T:Points (n+1)→ℂ)(v:ContinuousOn T (conf (n+1))): Integrable (fun x:α0_YL=> raysCostYL b i T (ledgeYL k a r p x.val)) (landRentYL α0_YL):=by
 haveI:= vestFinYL i b; haveI:=alphaFinYL; simp_rw [raysVisitYL]; exact (ScrollEarnYL a p b i k r h T v).integral_prod_left -- tune
lemma peakFTC_YL (F:Points n→ℂ)(S:Axis→Points (n+1)→ℂ) (u:ContDiffOn ℝ ∞ F (conf n))(v:∀ i,ContinuousOn (S i) (conf (n+1)))(e:∀ t∈α0_YL, D (mirDirYL k a) F (ledgeYL k a r p t)= ∑ i:Axis,raysCostYL b i (S i) (ledgeYL k a r p t)):
 F (ledgeYL k a r p 1)=F p+r • ∑ i:Axis,ScrollOpYL a p b i k r (S i):=by
 let L:= ledgeYL k a r p; let T (z:ℝ):= D (mirDirYL k a) F (L z)
 let H(z:ℝ):= r • T z; have he(x:ℝ)(v:x∈α0_YL): HasDerivAt (F ∘ L) (H x) x:=by
   have hz:= ((u _ (h x v).bounds).contDiffAt ((conf_open _).mem_nhds (h x v).bounds)).differentiableAt (by simp)
   have hu:= hz.hasFDerivAt.comp_hasDerivAt x (derLedgeYL a p k r x); rw [map_smul] at hu; exact hu
 have hf:IntervalIntegrable H volume 0 1:=by
    have hp: ContDiffOn ℝ ∞ (fderiv ℝ F) (conf n):= u.fderiv_of_isOpen (conf_open _) (by simp)
    have ht : ContinuousOn (fun x:ℝ => fderiv ℝ F (L x)) α0_YL:= hp.continuousOn.comp (ledgeSureYL a p k r).continuousOn fun x e=> (h x e).bounds
    have hv : ContinuousOn T α0_YL:= ht.clm_apply continuousOn_const
    exact (ContinuousOn.const_smul hv r).intervalIntegrable_of_Icc zero_le_one
 have Ht:= intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx=> he x (by simpa only [Set.uIcc_of_le (zero_le_one (α:=ℝ))] using hx)) hf
 haveI:=alphaFinYL
 have w : (∫ x:α0_YL,T x.val ∂landRentYL α0_YL)=∑ i:Axis, ScrollOpYL a p b i k r (S i):=by
    simp_rw [ScrollCubicYL a p b _ k r h (S _) (v _), ← integral_finsetSum _ (fun i _=>RayCubeYL a p b _ k r h (S i) (v i))] -- binder pattern `_` under lambda
    exact integral_congr_ae (Eventually.of_forall fun x=>e _ x.2)
 rw [←w,← integral_smul]
 change F (L 1)=F p+(∫ x:α0_YL,H x.val∂landRentYL α0_YL)
 rw [rayαYL H,Ht]; simp [Function.comp,L, ledgeYL]
#print axioms peakFTC_YL
end YM.GaugeFieldConstruction.Fathom

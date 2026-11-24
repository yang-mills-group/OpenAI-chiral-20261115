import GaugeFieldConstruction.PanoverRT
/-!
 # Single anchored motion on real ext. B spatial & 0≤support arc, tracked all observer coords & heights $
 # flux shutter center integral.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Mink Function Set Filter MeasureTheory Complex Finset Distribution Probe Surface NSF.Work.C20 Metric
open scoped Topology BigOperators ContDiff InnerProductSpace NNReal ENNReal
variable {n:ℕ}(k:Fin n)(y:Heights (n+1))(v:(τNearRT k).Fleck y)(g:Bool)
variable (Q:ZSideRt n→ℂ)(B:ContDiffBump (0:ℝ))(τ:Joint n)(x:Points n)
noncomputable abbrev PlotLuaTRt (ε:ℝ)(z:PlateTRt n):ℂ:= PenCostRt B τ z * Q (LuaιXRt k y g ε z.1 z.2)
noncomputable abbrev CapRiseTRt (r:ℝ):= closedBall (0:ℝ) r ×ˢ closedBall ((0:ℝ), x) r -- NOTE Prod metric max. tune tuple
lemma LuaZRt (s:ℝ): LuaιXRt k y g 0 s x=((s:ℂ), ΘOculusRt k y x):= by cases g<;>simp[LuaιXRt,αpayXRt] <;>rfl
lemma LuaZeroRt: LuaιXRt k y g 0 0 x = ΛArchRt k x y:=by simp [LuaZRt]
lemma EstambrePaintRT : Continuous (PenCostRt B τ):=(continuous_ofReal.comp ((shutterSmoothRt _).continuous.comp continuous_fst)).mul (τ.continuous.comp continuous_snd)
lemma PenCoverRt (d r:ℝ)(h:B.rOut≤d)(q:tsupport τ⊆ closedBall x r):tsupport (PenCostRt B τ) ⊆ closedBall (0:ℝ) d ×ˢ closedBall x r:=by
 refine closure_minimal ?_ (isClosed_closedBall.prod isClosed_closedBall); intro z hz
 refine ⟨closedBall_subset_closedBall h (shutterWidthRt B (subset_tsupport _ ?_)), q (subset_tsupport _ (right_ne_zero_of_mul hz))⟩
 intro w; apply hz; unfold PenCostRt; rw [show shutterXRt B z.1=0 from w]; simp
variable (r:ℝ)(t:0<r)(hB:B.rOut≤ r)(q:tsupport τ ⊆ closedBall x r)(w:∀ (p:ℝ × PlateTRt n), p∈CapRiseTRt x r→ AnalyticAt ℂ Q (LuaιXRt k y g p.1 p.2.1 p.2.2))
local notation "Κ"=> closedBall ((0:ℝ),x) r
local notation "I"=> closedBall (0:ℝ) r
local notation "Θon"=> PlotLuaTRt k y g Q B τ
include t hB w q
lemma SitsPenRt (ε:ℝ)(u:ε∈closedBall (0:ℝ) r):Integrable (Θon ε):=by
 have ht:tsupport (PenCostRt B τ) ⊆ Κ:=by rw [← closedBall_prod_same]; exact PenCoverRt B τ x r r hB q
 have h:Continuous (Θon ε):= continuous_iff_continuousAt.2 fun z=> by
    by_cases p:z∈Κ
    · exact (EstambrePaintRT B τ).continuousAt.mul ((w (ε,z) ⟨u,p⟩).continuousAt.comp (f:=fun z:PlateTRt n=> LuaιXRt k y g ε z.1 z.2) (x:=z) ((ContLuaRt k y g).continuousAt.comp (f:=fun z =>(ε,z)) (continuousAt_const.prodMk continuousAt_id))) -- tune
    apply continuousAt_const.congr (EventuallyEq.symm ?_ : (fun _:PlateTRt n=>(0:ℂ))=ᶠ[𝓝 z] Θon ε); filter_upwards [notMem_tsupport_iff_eventuallyEq.1 (mt (@ht z) p)] with b hb; exact mul_eq_zero_of_left hb _
 exact h.integrable_of_hasCompactSupport ( (show HasCompactSupport (PenCostRt B τ) from (isCompact_closedBall ..).of_isClosed_subset (isClosed_tsupport _) ht).mul_right)
lemma MayPenRT : ContinuousAt (fun ε:ℝ=>∫ z:PlateTRt n, PlotLuaTRt k y g Q B τ ε z) 0:=by
 have ht:tsupport (PenCostRt B τ) ⊆ Κ:=by rw [← closedBall_prod_same]; exact PenCoverRt B τ x r r hB q
 have h(z:ℝ × PlateTRt n)(p:z∈CapRiseTRt x r):ContinuousAt (fun z:ℝ ×PlateTRt n=> Θon z.1 z.2) z:= ((EstambrePaintRT _ _).comp continuous_snd).continuousAt.mul ((w _ p).continuousAt.comp (x:=z) (f:=fun z:ℝ ×PlateTRt n =>LuaιXRt k y g z.1 z.2.1 z.2.2) (ContLuaRt k y g).continuousAt)
 obtain ⟨D,hD⟩:= ( ((isCompact_closedBall (0:ℝ) r).prod (isCompact_closedBall ((0:ℝ),x) r)).image_of_continuousOn (fun z p=>(h z p|>.norm).continuousWithinAt)).bddAbove
 classical
 have hc(ε:ℝ)(z)(e:z∉Κ): Θon ε z=0:=mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport (mt (@ht z) e)) _
 let V:= Set.indicator Κ (fun _=>(max 0 D)); have hp:IsCompact Κ:= isCompact_closedBall ..
 have HD: Set.EqOn V (fun _=> max 0 D) Κ:=fun z v=> Set.indicator_of_mem v _
 refine tendsto_integral_filter_of_dominated_convergence V (Eventually.mono (closedBall_mem_nhds (0:ℝ) t) fun z v => (SitsPenRt k y g Q B τ x r t hB q w z v).1) ?_ ((integrableOn_const hp.measure_lt_top.ne).integrable_indicator hp.measurableSet) ?_
 · filter_upwards [closedBall_mem_nhds (0:ℝ) t] with ε u; refine Eventually.of_forall fun z=>?_
   by_cases k:z∈Κ
   · exact (hD ⟨(ε,z),⟨u,k⟩,rfl⟩).trans (le_trans (le_max_right _ D) (le_of_eq (HD k).symm))
   rw [hc _ _ k, norm_zero]; exact le_of_eq (Set.indicator_of_notMem k _).symm
 · refine Eventually.of_forall fun z=>?_
   by_cases p:z∈Κ
   · exact ((h (0,z) ⟨mem_closedBall_self t.le,p⟩).comp (x:=0) (f:=fun ε:ℝ => (ε,z)) (continuousAt_id.prodMk continuousAt_const)).tendsto
   simp_rw [hc _ z p]; exact tendsto_const_nhds
omit t hB w q
noncomputable abbrev woolTRt (x:ℝ):ℂ:= shutterXRt B x
lemma woolPaidRt:Integrable (woolTRt B):=by
 apply ((continuous_ofReal.comp ((shutterSmoothRt B).continuous)).integrable_of_hasCompactSupport); exact (shutterEndRt B).comp_left (by simp) -- tune
lemma woolWeightRt: (∫ x,woolTRt B x)=(-1:ℂ):=by
 let d:= B.rOut+1; have h:B.rOut<d:= by unfold d; linarith
 have h':0≤d:= (B.rOut_pos.trans h).le
 have hu: (∫ x,woolTRt B x)= (∫ x in (0:ℝ)..d, woolTRt B x):=by
    rw [intervalIntegral.integral_of_le h', setIntegral_eq_integral_of_forall_compl_eq_zero]; intro s e
    by_cases p:s≤0; · unfold woolTRt; rw [show shutterXRt B s=0 from (shutterPRt B _ p).eq_of_nhds]; simp
    have hp:d<s:=lt_of_not_ge fun a=> e ⟨lt_of_not_ge p,a⟩; unfold woolTRt; rw [show shutterXRt B s=0 from image_eq_zero_of_notMem_tsupport (fun v=> ?_)]; swap; · exact not_le.mpr (h.trans hp) (by simpa [abs_of_pos (lt_of_not_ge p)] using shutterWidthRt B v)
    simp
 let W(s:ℝ):ℂ:= B s; have hw:Continuous W:= continuous_ofReal.comp B.continuous
 rw[hu, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h' hw.continuousOn (?_) (woolPaidRt B).intervalIntegrable]
 · have t: d∉ closedBall (0:ℝ) B.rOut:=by simp [abs_of_nonneg h',h]
   simp [W,show B d=0 from image_eq_zero_of_notMem_tsupport (show d ∉ tsupport ↑B from by rw [B.tsupport_eq]; exact t), show B (0:ℝ)=1 from B.eventuallyEq_one.eq_of_nhds ]
 intro x hx; unfold woolTRt; rw [show shutterXRt _ _=_ from (shutterTRt B x hx.1).eq_of_nhds]; exact ofRealCLM.hasFDerivAt.comp_hasDerivAt x ((B.contDiff.differentiable (n:=∞) (by simp) _).hasDerivAt)
#print axioms woolWeightRt
end YM.NSF.Boundary
end

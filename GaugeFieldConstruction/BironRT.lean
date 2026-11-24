import GaugeFieldConstruction.OpalRT
/-!
 # Shelter lemma. If Q(z) on half-plane F signatures has hol slope extending across as germ, integrate to provide full extension in joint variables.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.PortRT
open Filter Set MeasureTheory Function Topology Metric Complex Module AffineMap
open scoped BigOperators Topology ContDiff NNReal ENNReal
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E]
variable (x : E)(U:Set ℂ)(hU:IsOpen U)(cU:Convex ℝ U)(eU:(0:ℂ)∈ closure U)
variable (F H : ℂ×E→ℂ)
local notation "z"=> ((0:ℂ),x)
abbrev WetαRt (F:ℂ×E→ℂ) (u:ℂ×E):= fderiv ℂ F u (1,0)
variable (hH:AnalyticAt ℂ H (0,x))(h:∀ᶠ v:ℂ×E in 𝓝[U ×ˢ univ] ((0:ℂ),x), AnalyticAt ℂ F v ∧ WetαRt F v=H v)
-- Line_R calculation.
variable (a b:ℂ)
noncomputable def LaneRT (t:ℝ): ℂ:= t • (b-a) + a
lemma LaneIRT (c:Convex ℝ U)(p:a∈U)(w:b∈U)(t:ℝ)(i:t∈ Icc (0:ℝ) 1): LaneRT a b t∈U:= by
 have e: LaneRT a b t=(1-t) • a + t • b:=by unfold LaneRT; rw [smul_sub,sub_smul,one_smul]; abel
 rw [e]; exact c p w (by linarith [i.2]) i.1 (by ring)
noncomputable def PondRT (a:ℂ)(r:ℝ)(p:ℂ×E):= (LaneRT a p.1 r,p.2)
lemma PondRaceRT:Continuous (fun p:(ℂ×E)×ℝ=> PondRT a p.2 p.1):=by unfold PondRT LaneRT; fun_prop
noncomputable def TrailRT (r:ℝ): ℂ × E →L[ℂ] ℂ×E:= ((r:ℂ) • ContinuousLinearMap.fst ℂ ℂ E).prod (ContinuousLinearMap.snd ℂ ℂ E)
lemma PondFormRt (r:ℝ)(p:ℂ×E): PondRT a r p= TrailRT r p + (LaneRT a 0 r,0):=by
 ext1; · simp [PondRT,LaneRT,TrailRT, Complex.real_smul]; ring
 simp[PondRT,TrailRT]
lemma TrailContRT: Continuous (fun t:ℝ=> (TrailRT t: ℂ×E→L[ℂ] ℂ×E)):=by
 let I:= ContinuousLinearMap.fst ℂ ℂ E; let K:= ContinuousLinearMap.inl ℂ ℂ E ∘L I; let Q:= ContinuousLinearMap.inr ℂ ℂ E ∘L (ContinuousLinearMap.snd ℂ ℂ E)
 have p(t:ℝ): TrailRT t=(t:ℂ) • K+Q:=ContinuousLinearMap.ext fun s=>by simp [TrailRT,K,Q,I]
 simp_rw [p]; exact (continuous_ofReal.smul continuous_const).add continuous_const
-- segment FTC note use subscript real injection
lemma SegmentZRTR (w:E)(r:∀ t:ℝ,t∈ Icc (0:ℝ) 1 → AnalyticAt ℂ F (PondRT a t (b,w)) ∧ WetαRt F (PondRT a t (b,w))= H (PondRT a t (b,w)) ∧ AnalyticAt ℂ H (PondRT a t (b,w)) ):
    F (a,w)+(b-a)*(∫ t:ℝ in Icc 0 1, H (PondRT a t (b,w)))= F (b,w):=by
 let S(t:ℝ):ℂ×E:=PondRT a t (b,w); have c:Continuous S:= (PondRaceRT a).comp (continuous_const.prodMk continuous_id)
 have Hα : ContinuousOn (fun t:ℝ=> (b-a)*H (S t)) (Icc 0 1) := fun t kt => ContinuousAt.continuousWithinAt ((r t kt).2.2.continuousAt.comp (f:=S) c.continuousAt|>.const_mul (b-a))
 have pu(t:ℝ)(p:t∈ Icc (0:ℝ) 1): HasDerivAt (fun s:ℝ=> F (S s)) ((b-a)*H (S t)) t:=by
    -- restrict complex maps w arbitrary without normReal E assumption: local restriction.
    let L(s:ℂ):=F (s,w); 
    let J:=LaneRT a b t; have ht:HasDerivAt (fun v:ℂ=>(v,w)) (1,0) J:= (hasDerivAt_id' J).prodMk (hasDerivAt_const ..)
    have he:HasDerivAt L (H (S t)) J:= (((r t p).1.differentiableAt.hasFDerivAt.comp_hasDerivAt J ht)).congr_deriv ((r t p).2.1)
    have hs : HasDerivAt (LaneRT a b) (b-a) t:=by
       convert! ((hasDerivAt_id' t).smul_const (b-a)).add_const a using 1; simp
    have hz:HasDerivAt (L ∘ LaneRT a b) _ t:= (he.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hs; exact hz.congr_deriv (by simp [mul_comm])
 rw[integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (zero_le_one' ℝ),← intervalIntegral.integral_const_mul] -- tune
 have ht : Icc (0:ℝ) 1= uIcc 0 1:= (uIcc_of_le (by norm_num)).symm; rw [ht] at Hα pu; change F _ + (∫ t:ℝ in 0..1,(b-a)*H (S t))=_; rw[intervalIntegral.integral_eq_sub_of_hasDerivAt pu Hα.intervalIntegrable]; simp [S,PondRT,LaneRT]
include eU cU hU h hH
lemma shelterXRt: ∃ G:ℂ × E→ℂ,AnalyticAt ℂ G (0,x) ∧ G =ᶠ[𝓝[U ×ˢ univ] ((0:ℂ),x)] F ∧ WetαRt G =ᶠ[𝓝 ((0:ℂ),x)] H:=by
 classical
 have h' := hH.eventually_analyticAt.and (eventually_nhdsWithin_iff.1 h)
 obtain ⟨d,hd,hD⟩:= Metric.mem_nhds_iff.mp h'
 let V:= ball (0:ℂ) d; let W:=ball x d; let D:=V ×ˢ W
 have eq:D=ball z d:= ball_prod_same ..
 have hZ:z ∈ D:=eq.symm ▸ mem_ball_self hd
 obtain ⟨u,p,i⟩:= mem_closure_iff_nhds.1 eU V (ball_mem_nhds _ hd) -- yields Inter pair
 have hp(q:ℂ×E)(r:q∈D): AnalyticAt ℂ H q ∧ (q.1∈U→AnalyticAt ℂ F q ∧ WetαRt F q=H q):=by
    have ht:= hD (eq ▸ r); exact ⟨ht.1,fun b=>ht.2 ⟨b,mem_univ _⟩⟩
 let δ:= fun y:ℂ×E=> ∫ t:ℝ in Icc 0 1,H (PondRT u t y)
 have he (y:ℂ×E)(t:ℝ)(l:t∈Icc (0:ℝ) 1)(s:y∈D):PondRT u t y∈D:=⟨LaneIRT V u y.1 (convex_ball ..) p s.1 t l,s.2⟩ -- tune binder
 have hv: AnalyticAt ℂ δ z:=by
    let K:= Icc (0:ℝ) 1
    let U₀(q:ℂ×E)(t:ℝ):=H (PondRT u t q); let U₁(q:ℂ×E)(t:ℝ):=(fderiv ℂ H (PondRT u t q) ∘L TrailRT t)
    refine SwellAnalyticRT (A:=D) (K:=K) (μ:=volume) (Metric.isOpen_ball.prod Metric.isOpen_ball) isCompact_Icc measurableSet_Icc (Subset.refl _) U₀ U₁ ?_ ?_ ?_ _ hZ
    · exact fun v a=> ((hp _ (he _ v.2 a.2 a.1)).1.continuousAt.comp (f:=fun p:(ℂ × E) × ℝ=> PondRT u p.2 p.1) ((PondRaceRT (E:=E) u).continuousAt (x:=v))).continuousWithinAt
    · refine fun v a=> ContinuousAt.continuousWithinAt ?_
      exact (((hp _ (he _ v.2 a.2 a.1)).1.fderiv.continuousAt.comp (f:=fun v:(ℂ×E)×ℝ=>PondRT u v.2 v.1) ((PondRaceRT (E:=E) u).continuousAt (x:=v))).clm_comp (TrailContRT (E:=E) |>.comp continuous_snd |>.continuousAt))
    intro y s j l; apply ((hp _ (he _ _ l s)).1.differentiableAt.hasFDerivAt).comp y (f:=PondRT u j)
    simp_rw [funext (PondFormRt (E:=E) u j)]; exact (TrailRT (E:=E) j).hasFDerivAt.add_const _
 let G(y:ℂ × E):= F (u,y.2) + (y.1-u)*δ y
 have hz: (u,x)∈D:= ⟨p,mem_ball_self hd⟩
 have hc:AnalyticAt ℂ G z:= (((hp _ hz).2 i).1.comp (f:=fun q:ℂ × E=> (u,q.2)) ((contDiffAt_const.prodMk (contDiffAt_snd (𝕜:=ℂ))).analyticAt)).add ((((contDiffAt_fst (𝕜:=ℂ)).analyticAt).sub analyticAt_const).mul hv)
 have hh(y:ℂ×E)(s:y∈D)(w:y.1∈U): G y= F y:=by
    refine SegmentZRTR F H u _ _ (fun t p=>?_)
    have ha: (PondRT u t y).1∈ U:= LaneIRT U u y.1 cU i w t p
    have ht:= hp _ (he _ _ p s); exact ⟨(ht.2 ha).1,(ht.2 ha).2,ht.1⟩
 let S:= U ×ˢ (univ:Set E); have ho:IsOpen S:= hU.prod isOpen_univ
 have hs : D∈𝓝 z:=eq.symm ▸ ball_mem_nhds _ hd
 have H':G =ᶠ[𝓝[S] z] F:=by filter_upwards [self_mem_nhdsWithin, Eventually.filter_mono nhdsWithin_le_nhds hs] with y hy u; exact hh y u hy.1
 refine ⟨G,hc,H',?_⟩
 have ht : WetαRt G =ᶠ[𝓝[S] z] H:=by filter_upwards [h, self_mem_nhdsWithin,eventually_eventually_nhdsWithin.2 H'] with y t l e; change G=ᶠ[𝓝[S] y] F at e; rw [ho.nhdsWithin_eq l] at e; exact (show WetαRt G y=WetαRt F y from congrArg (fun D: _→L[ℂ]_=> D (1,0)) e.fderiv_eq).trans t.2
 have hw: AnalyticAt ℂ (WetαRt G) z:=((ContinuousLinearMap.apply ℂ ℂ ((1:ℂ),(0:E))).analyticAt _).comp hc.fderiv
 obtain ⟨r,p,hT⟩:= Metric.mem_nhds_iff.mp ((hw.eventually_analyticAt.and hH.eventually_analyticAt).and (eventually_nhdsWithin_iff.1 ht))
 have hC:z∈closure S:=by simp only [S,closure_prod_eq,closure_univ]; exact ⟨eU,mem_univ _⟩
 obtain ⟨b,u,w⟩:=mem_closure_iff_nhds.1 hC (ball z r) (ball_mem_nhds _ p)
 have hs: Set.EqOn (WetαRt G) H (ball z r):=(show AnalyticOnNhd ℂ (WetαRt G) (ball z r) from fun x s=>(hT s).1.1).eqOn_of_preconnected_of_eventuallyEq (fun x s=>(hT s).1.2) ((convex_ball z r).isPreconnected) u ?_
 · filter_upwards [ball_mem_nhds z p] with x hx; exact hs hx
 filter_upwards [(ho.mem_nhds w),Metric.isOpen_ball.mem_nhds u] with y h k; exact (hT k).2 h
#print axioms shelterXRt
end YM.PortRT
end

import GaugeFieldConstruction.BeatificQc
/-!
# Moving, thinner cutoff replacing a fixed bulb
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom.Salam
open Function Filter Set TopologicalSpace YM Analysis MeasureTheory Points Bulb Payroll Metric
open scoped Topology BigOperators ContDiff Classical
variable {n : ℕ}
noncomputable def PupaQc :ContDiffBump (0:E4):= ⟨5/4,3/2,by norm_num,by norm_num⟩
noncomputable def DokiQc : Bulb:= ⟨PupaQc,PupaQc.contDiff,PupaQc.hasCompactSupport⟩
local notation "W"=> DokiQc
lemma DockQc : lit W 0:= PupaQc.eventuallyEq_one_of_mem_ball (mem_ball_self PupaQc.rIn_pos)
lemma faultQc {x:E4}(h:x∈ DokiQc.shore): AnnulusQc 1 x:=by
 have t: PupaQc.rIn ≤ ‖x‖:=by
    by_contra! e; exact (Bulb.centre (b:=W) (x:=x) (PupaQc.eventuallyEq_one_of_mem_ball (mem_ball_zero_iff.mpr e))) h
 have e':‖x‖ ≤ PupaQc.rOut:=by
    have v:x∈ tsupport PupaQc:= strands (b:=W) h; rw[PupaQc.tsupport_eq] at v; exact mem_closedBall_zero_iff.mp v
 exact ⟨lt_of_lt_of_le (show (1:ℝ)<PupaQc.rIn by unfold PupaQc; norm_num) t,lt_of_le_of_lt e' (show PupaQc.rOut<(2:ℝ)*1 by unfold PupaQc; norm_num)⟩
lemma helm_consQ (z:E4)(x:Points n): (helm (cons z x),riders (cons z x))=(z,x):=(fuse (n:=n)).apply_symm_apply (z,x)
-- scaled bump
noncomputable def dockScaleQc (e:ℝ) (p:0<e): Bulb where
 f x:= W (e⁻¹ • x)
 d:= by
     refine DokiQc.d.comp ?_
     change ContDiff ℝ ∞ (fun x:E4=> e⁻¹ • x); fun_prop
 c:= by
    apply HasCompactSupport.comp_homeomorph DokiQc.c (Homeomorph.smulOfNeZero e⁻¹ (inv_ne_zero p.ne')) -- tune
lemma dockCostQc (z:ℝ)(e:0<z)(x:E4)(i:Axis): D (basis i) (dockScaleQc z e).f x=z⁻¹*D (basis i) DokiQc.f (z⁻¹ • x):=by
 let L:E4→L[ℝ] E4:= z⁻¹ • ContinuousLinearMap.id ℝ E4
 change fderiv ℝ (DokiQc.f ∘ L) x (basis i)=_; rw [fderiv_comp _ (DokiQc.d.differentiable (by simp) _) L.differentiableAt,L.fderiv]; rw [ContinuousLinearMap.comp_apply]; change fderiv ℝ DokiQc.f (L x) (z⁻¹ • basis i)=_; rw [map_smul]; rfl
lemma dockLitQc (z:ℝ)(e:0<z): (dockScaleQc z e).lit 0:= by
 have h (t:ℝ): ContinuousAt (fun x:E4=> t • x) 0:=(continuous_id.const_smul t).continuousAt
 have v:Tendsto (fun x:E4=> z⁻¹ • x) (𝓝 0) (𝓝 (0:E4)):=by simpa using (h z⁻¹).tendsto
 exact v.eventually DockQc
lemma dockLowQc (z:ℝ)(e:0<z)(x:E4)(p:x∈run (dockScaleQc z e)): ‖x‖≤2*z:=by
 have ht:z⁻¹ • x ∈ tsupport PupaQc:= by
   let L:=fun x:E4=>z⁻¹ • x; have h:Continuous L:=continuous_id.const_smul (z⁻¹); exact closure_mono (show L '' support (dockScaleQc z e).f ⊆ support (⇑PupaQc) from Set.image_subset_iff.mpr (fun x q=>by exact q)) (mem_closure_image h.continuousAt p)
 rw [PupaQc.tsupport_eq] at ht; have v:= mem_closedBall_zero_iff.mp ht; rw [norm_smul, Real.norm_eq_abs,abs_of_nonneg (inv_pos.mpr e).le] at v
 have he : z⁻¹ * ‖x‖ ≤ 2:=le_trans v (by unfold PupaQc; norm_num)
 rwa [mul_comm,←div_eq_mul_inv,div_le_iff₀ e] at he

-- pair z x. Target first
variable (b : Bulb)(p : Test (n+1))(a:Bulb)
def LengthQc : Points (n+2)→L[ℝ] E4 := helm-Payroll.loc 0 ∘L riders
lemma LengthCostQc (i) : LengthQc (n:=n) (direction 0 i)=basis i:=by simp only[LengthQc,ContinuousLinearMap.sub_apply,head_on,ContinuousLinearMap.comp_apply,on_left,map_zero,sub_zero] -- comp tuning
lemma lengthBpQc (z:E4)(x:Points (n+1)):LengthQc (cons z x)=z-x 0:=by
 obtain h:=helm_consQ z x; rw[LengthQc,ContinuousLinearMap.sub_apply, Prod.mk.inj h|>.1,ContinuousLinearMap.comp_apply,Prod.mk.inj h|>.2]; rfl
noncomputable def slipQc (x:Points (n+2)):ℂ:= (b (helm x)-a (LengthQc x)) • p (riders x)
lemma slipSmoothQc : ContDiff ℝ ∞ (slipQc b p a):= ((b.d.comp helm.contDiff).sub (a.d.comp LengthQc.contDiff)).smul (p.contDiff.comp riders.contDiff)
lemma slipCompactQc : HasCompactSupport (slipQc b p a):=by
 let T:=tsupport p; have hu:IsCompact T:=p.hasCompactSupport; let B:= ((fuse (n:=n+1)).symm '' (b.run ×ˢ T)); let L:=fun t:E4×Points (n+1)=> LensQc t.1 t.2; let A:= L '' (a.run ×ˢ T)
 refine HasCompactSupport.intro (( (show IsCompact b.run from b.c).prod hu).image fuse.symm.continuous |>.union (((show IsCompact a.run from a.c).prod hu).image lensContinuousQc)) ?_
 intro x p'; change x ∉ B ∪ A at p'; unfold slipQc
 by_cases q: riders x ∈T
 · have h: helm x ∉ b.run:= fun i=> p' (Or.inl ⟨_,⟨i,q⟩,(fuse.symm_apply_apply x)⟩)
   have he: LengthQc x∉ a.run:=by
     intro i; refine p' (Or.inr ⟨(LengthQc x,riders x),⟨i,q⟩,?_⟩)
     let X:= riders x; let Y:=LengthQc x; change LensQc Y X=x; unfold LensQc; have hh:head X +Y=helm x:=by unfold Y LengthQc; rw [ContinuousLinearMap.sub_apply]; change head X+(helm x-head X)=_; rw [add_sub_cancel]
     rw [hh]; exact fuse.symm_apply_apply x
   rw [image_eq_zero_of_notMem_tsupport (f:=⇑b) h,image_eq_zero_of_notMem_tsupport (f:=⇑a) he]; simp
 rw [image_eq_zero_of_notMem_tsupport (f:=p) q]; simp
-- a round x won't touch others. collars
structure RespectQc : Prop where
  lit: lit a 0
  excludes:∀ x ∈tsupport p,∀ j:Fin n, x j.succ - x 0 ∉ a.run
lemma RespLateQc (e:ℕ→ℝ)(v:∀i,0<e i)(h:Tendsto e atTop (𝓝 0)) : ∀ᶠ i in atTop, RespectQc p (dockScaleQc (e i) (v i)):=by
 have he:∀ᶠ t:ℝ in 𝓝 0,∀ x∈ tsupport p,∀ i:Fin n,2*t< ‖x i.succ-x 0‖:=(show IsCompact _ from p.hasCompactSupport).eventually_forall_of_forall_eventually (fun x hx => eventually_all.mpr (fun i=> by
    have h:= (show x∈conf _ from p.tsupport_subset hx).ne i.succ_ne_zero
    have q:2*(0:ℝ)< ‖x i.succ-x 0‖:=by rw [mul_zero,norm_pos_iff]; exact sub_ne_zero.mpr h
    exact (isOpen_lt (continuous_const.mul continuous_fst) (((loc i.succ).continuous.comp continuous_snd).sub ((loc 0).continuous.comp continuous_snd)).norm).mem_nhds q))
 filter_upwards [h.eventually he] with i v'
 exact ⟨dockLitQc _ _,fun x hx j q=> (v' x hx j).not_ge (dockLowQc _ _ _ q)⟩
lemma slipConfQc (h:Works b p 0)(q:RespectQc p a): tsupport (slipQc b p a) ⊆ conf _:=by
 let T:=tsupport p
 have v: tsupport (slipQc b p a) ⊆ riders ⁻¹' T:= closure_minimal (fun x h=>by
    by_contra w; exact h (by change (b _-a _) • _=0; rw [image_eq_zero_of_notMem_tsupport (f:=p) (show riders x∉T from w), smul_zero])) ((isClosed_tsupport _).preimage riders.continuous)
 intro x k
 have hv: riders x∈ T:= v k
 let u:= riders x; have t: LengthQc x=helm x-u 0:=rfl
 apply first_conf _ (p.tsupport_subset hv); intro i; refine Fin.cases ?_ ?_ i
 · intro i; have ht: b =ᶠ[𝓝 (helm x)] fun _=>1:= i ▸ h.bulb u hv
   have he: LengthQc x=0:=by rw[t, show u 0=_ from i,sub_self];
   apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) k
   filter_upwards [helm.continuous.continuousAt.tendsto.eventually ht, LengthQc.continuous.continuousAt.tendsto.eventually (show a =ᶠ[𝓝 (LengthQc x)] fun _=>1 from he.symm ▸ q.lit)] with y a' e
   change b _=1 at a'; change a _=1 at e; change (_-_ ) • _=0; rw [a',e,sub_self,zero_smul]
 intro j i
 have ht:=h.direct u hv j.succ j.succ_ne_zero; have h: b =ᶠ[𝓝 (helm x)] 0:= notMem_tsupport_iff_eventuallyEq.mp (i ▸ ht)
 have he: a =ᶠ[𝓝 (LengthQc x)] 0 := notMem_tsupport_iff_eventuallyEq.mp (show LengthQc x∉ a.run from (by rw[t,←show u j.succ=helm x from i]; exact q.excludes u hv j))
 apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) k
 filter_upwards [helm.continuous.continuousAt.tendsto.eventually h,LengthQc.continuous.continuousAt.tendsto.eventually he] with y v e; change b _=0 at v; change a _=0 at e; change (_-_ ) • _=0; rw [v,e,sub_self,zero_smul]
noncomputable def PokerQc (h:Works b p 0)(q:RespectQc p a):Test (n+2):=⟨slipQc b p a,slipSmoothQc ..,slipCompactQc ..,slipConfQc b p a h q⟩
#print axioms faultQc
#print axioms slipConfQc
#print axioms RespLateQc
end YM.GaugeFieldConstruction.Fathom.Salam

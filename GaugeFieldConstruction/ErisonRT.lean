import GaugeFieldConstruction.ToneVestRT
import GaugeFieldConstruction.CodaMars
/-!
 # Temporal shutters and spatial shades. SAME bumps B and f; generate Bulb & Hatch. Validity: Breather iff other fields OUT; sufficient strict other times with β width. HATCH need temporal < rIn spatial so causal cone misses. Does not take f to infinity.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Mink Function Set Filter MeasureTheory Complex Finset Distribution Probe Surface GaugeFieldConstruction.Fathom Metric
open scoped Topology BigOperators ContDiff InnerProductSpace NNReal ENNReal
variable (B : ContDiffBump (0:ℝ))(f: ContDiffBump (0:Space3))
noncomputable def UpShadeRt (B:ContDiffBump (0:ℝ))(f:ContDiffBump (0:Space3))(o:E4): Bulb where
 f v:= B (time (v-o)) * f (spatial (v-o))
 d:= (B.contDiff.comp (clockL.contDiff.comp (contDiff_id.sub contDiff_const))).mul (f.contDiff.comp (restL.contDiff.comp (contDiff_id.sub contDiff_const)))
 c:=by
    have h: HasCompactSupport (fun q:Space3 × ℝ => B q.2 * f q.1):=HasCompactSupport.of_support_subset_isCompact (f.hasCompactSupport.prod B.hasCompactSupport) fun x v=> ⟨subset_tsupport ⇑f (right_ne_zero_of_mul v),subset_tsupport ⇑B (left_ne_zero_of_mul v)⟩
    exact (h.comp_homeomorph divide.toHomeomorph).comp_homeomorph (Homeomorph.subRight o)
#print axioms UpShadeRt
variable (o v:E4)
local notation "Φ_L"=> UpShadeRt
lemma ΦshadeTIRT: YM.Analysis.D (basis timeAxis) ((Φ_L B f o).f) v= deriv B (time (v-o)) * f (spatial (v-o)):=by
 let F:= clockL; let S:=restL; let t:E4:=v-o
 have he:HasFDerivAt (fun v=>v-o) (ContinuousLinearMap.id ℝ E4) v:= (hasFDerivAt_id v).sub_const o
 have h(B':ℝ): HasDerivAt B (deriv B B') B':= (B.contDiff.differentiable (n:=∞) (by simp) B').hasDerivAt
 unfold YM.Analysis.D; rw [show (Φ_L B f o).f=(B ∘ F ∘ fun v=> v-o)*(f ∘ S ∘ fun v=>v-o) from rfl, (((h _).hasFDerivAt.comp v ((F.hasFDerivAt).comp v he)).mul (((f.contDiff.differentiable (n:=∞) (by simp) (S t)).hasFDerivAt).comp v (S.hasFDerivAt.comp v he))).fderiv]; simp [F,S,t,mul_comm]
lemma ΦshadeSIRT (i:Fin 3): YM.Analysis.D (basis i.castSucc) ((Φ_L B f o).f) v= B (time (v-o))* fderiv ℝ f (spatial (v-o)) (skyIRT i):=by
 let F:= clockL; let S:=restL; let t:E4:=v-o
 have he:HasFDerivAt (fun v=>v-o) (ContinuousLinearMap.id ℝ E4) v:= (hasFDerivAt_id v).sub_const o
 have h(B':ℝ): HasDerivAt B (deriv B B') B':= (B.contDiff.differentiable (n:=∞) (by simp) B').hasDerivAt
 unfold YM.Analysis.D; rw [show (Φ_L B f o).f=(B ∘ F ∘ fun v=> v-o)*(f ∘ S ∘ fun v=>v-o) from rfl, (((h _).hasFDerivAt.comp v ((F.hasFDerivAt).comp v he)).mul (((f.contDiff.differentiable (n:=∞) (by simp) (S t)).hasFDerivAt).comp v (S.hasFDerivAt.comp v he))).fderiv]; simp [F,S,t,mul_comm,skyIRT]
lemma ΦcoverRt: (Φ_L B f o).lit o:= by
 have hc:Tendsto (fun v:E4=>v-o) (𝓝 o) (𝓝 0):=by simpa using (show Continuous fun v=>v-o by fun_prop).tendsto o
 filter_upwards [B.eventuallyEq_one.comp_tendsto ((show Tendsto time (𝓝 0) (𝓝 0) from by simpa using clock_cont.tendsto 0).comp hc), f.eventuallyEq_one.comp_tendsto ((show Tendsto spatial (𝓝 0) (𝓝 0) from by simpa using rest_cont.tendsto 0).comp hc)] with y hy h
 change B _ * f _=_; rw [show B (time (y-o))=1 from hy,show f (spatial (y-o))=1 from h,one_mul] -- tune
lemma ΦboundRt (u:v∈ (Φ_L B f o).run): time v-time o ∈ closedBall (0:ℝ) B.rOut:=by
 have he(v:E4): time (v-o)=time v-time o:=map_sub clockL ..
 refine closure_minimal (t:= (fun v:E4=>time v-time o) ⁻¹' closedBall 0 B.rOut) ?_ (isClosed_closedBall.preimage (by fun_prop)) u
 intro y h; change time y-time o ∈ closedBall 0 B.rOut; rw [← he, ← B.tsupport_eq]; exact subset_tsupport ⇑B (left_ne_zero_of_mul h)
variable {n:ℕ}
lemma ΦinhaleRt (k:Fin n)(p:Points n)(t:p∈ conf n)(h:∀ j,j≠k → time (p j)-time (p k) ∉ closedBall (0:ℝ) B.rOut): BreatherMars (Φ_L B f (p k)) k p:= ⟨t, ΦcoverRt .., fun j l hp=> h j l (ΦboundRt _ _ _ _ hp)⟩
#print axioms ΦinhaleRt
noncomputable def shutterXRt (x:ℝ):ℝ:= if 0<x then deriv B x else 0
lemma shutter0Rt : shutterXRt B =ᶠ[𝓝 0] 0:=by
 filter_upwards [B.eventuallyEq_one.deriv] with x hx
 unfold shutterXRt; rw [hx,show deriv (1:ℝ→ℝ) x=0 from deriv_const _ _]; simp
lemma shutterPRt (x:ℝ)(p:x≤0): shutterXRt B=ᶠ[𝓝 x] 0:=by
 rcases p.lt_or_eq with p|p; · filter_upwards [gt_mem_nhds p] with x hx; simp [shutterXRt,not_lt_of_gt hx]
 rw [p]; exact shutter0Rt B
lemma shutterTRt (x:ℝ)(p:0<x): shutterXRt B=ᶠ[𝓝 x] deriv B:=by
 filter_upwards [lt_mem_nhds p] with x hx; exact if_pos hx
lemma shutterWidthRt: tsupport (shutterXRt B) ⊆ closedBall (0:ℝ) B.rOut:=by
 rw[← B.tsupport_eq]; refine (closure_mono (t:= Function.support (deriv B)) ?_).trans tsupport_deriv_subset; intro x h t; exact h (by simp [shutterXRt, show deriv B x=0 from t])
lemma shutterEndRt: HasCompactSupport (shutterXRt B):=(isCompact_closedBall ..).of_isClosed_subset (isClosed_tsupport _) (shutterWidthRt _)
lemma shutterSmoothRt:ContDiff ℝ ∞ (shutterXRt B):= contDiff_iff_contDiffAt.mpr fun x=>by
 rcases lt_or_ge 0 x with p|p
 · exact ((show ContDiffAt ℝ ∞ (deriv B) x from (((show ContDiffAt ℝ ∞ (B:ℝ→ℝ) x from B.contDiff.contDiffAt).fderiv_right (by simp)).clm_apply contDiffAt_const))).congr_of_eventuallyEq (shutterTRt _ _ p)
 exact contDiffAt_const.congr_of_eventuallyEq (shutterPRt _ _ p)
abbrev shimmeringRt (b:Bulb):Test4:=(b.c.comp_left (g:=Complex.ofRealCLM) (map_zero _)).toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.d)
noncomputable def padRt: Test4:=shimmeringRt (Φ_L B f 0)
noncomputable def χWarmRt: Bulb where
 f v:= shutterXRt B (time v) * f (spatial v)
 d:= ((shutterSmoothRt B).comp clockL.contDiff).mul (f.contDiff.comp restL.contDiff)
 c:=by
    have h: HasCompactSupport (fun q:Space3 × ℝ => shutterXRt B q.2 * f q.1):=HasCompactSupport.of_support_subset_isCompact (f.hasCompactSupport.prod (shutterEndRt B)) fun x v=> ⟨subset_tsupport ⇑f (right_ne_zero_of_mul v),subset_tsupport (shutterXRt B) (left_ne_zero_of_mul v)⟩
    exact h.comp_homeomorph divide.toHomeomorph
noncomputable def αWarmRt(i:Axis):Test4:= if i=timeAxis then shimmeringRt (χWarmRt B f) else 0
lemma PinGlowRT : DmoveRT timeAxis (padRt B f) v=↑(deriv B (time v))* (f (spatial v):ℂ):=by
 unfold DmoveRT; rw [ΦsΛKnownL]; let F:=Φ_L B f 0
 rw [show (⇑(padRt B f))= (Complex.ofRealCLM) ∘ F.f from rfl, (Complex.ofRealCLM.hasFDerivAt.comp v (F.d.differentiable (by simp) v).hasFDerivAt).fderiv]; simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]; change ((YM.Analysis.D _ (Φ_L B f 0).f v:ℝ):ℂ)=_; simp [ΦshadeTIRT]
lemma PinSideRT (i:Fin 3): DmoveRT i.castSucc (padRt B f) v=(B (time v):ℂ)* (fderiv ℝ f (spatial v) (skyIRT i):ℝ):=by
 unfold DmoveRT; rw [ΦsΛKnownL]; let F:=Φ_L B f 0
 rw [show (⇑(padRt B f))= (Complex.ofRealCLM) ∘ F.f from rfl, (Complex.ofRealCLM.hasFDerivAt.comp v (F.d.differentiable (by simp) v).hasFDerivAt).fderiv]; simp only [ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply]; change ((YM.Analysis.D _ (Φ_L B f 0).f v:ℝ):ℂ)=_; simp [ΦshadeSIRT]
lemma foneArchRt (x: Space3)(t: ‖x‖<f.rIn): f =ᶠ[𝓝 x] fun _=>1:=by
 filter_upwards [isOpen_ball.mem_nhds (show x∈ball 0 f.rIn from by simpa using t)] with x h; exact f.one_of_mem_closedBall (ball_subset_closedBall h)
lemma BornUnderRT (t:B.rOut<f.rIn): HatchRT (padRt B f) (αWarmRt B f):=by
 refine ⟨(Φ_L B f 0).c.comp_left (g:=Complex.ofRealCLM) (map_zero _),fun i=>?_,?_,fun i v h p=>?_,fun i v h p=>?_⟩
 · by_cases p:i=timeAxis
   · rw [αWarmRt,if_pos p]; exact (χWarmRt B f).c.comp_left (g:=Complex.ofRealCLM) (map_zero _)
   rw [αWarmRt,if_neg p]; change HasCompactSupport (0:E4→ℂ); simp [HasCompactSupport]
 · filter_upwards [ΦcoverRt B f 0] with x hx; change ((Φ_L B f 0).f x:ℂ)=1; rw [show (Φ_L B f 0).f x=1 from hx, Complex.ofReal_one]
 · cases i using Fin.lastCases with
   | last=> change _=ᶠ[_] ⇑(DmoveRT timeAxis _)
            filter_upwards [((clock_cont.tendsto v).eventually (shutterTRt B _ p))] with y hy; change (αWarmRt _ _ _) y=_; rw [PinGlowRT B f, αWarmRt, if_pos (show _ from rfl)] -- tune
            change ((shutterXRt B (time y) * f (spatial y):ℝ):ℂ)=_; simp [show shutterXRt B (time y)= deriv B (time y) from hy] -- tune
   | cast i=>skip
             rw [αWarmRt,if_neg (Fin.castSucc_ne_last i)]; by_cases q: time v∈closedBall (0:ℝ) B.rOut
             · have hx: ‖spatial v‖≤|time v|:=not_lt.mp fun r=>h ((lateral v).mpr r)
               have hV: ‖spatial v‖< f.rIn:= (hx.trans (by simpa using q)).trans_lt t
               filter_upwards [((rest_cont.tendsto v).eventually ((foneArchRt f _ hV).fderiv (𝕜:=ℝ)))] with y hy; rw [PinSideRT]; rw [show fderiv ℝ f (spatial y)=0 from hy.trans (fderiv_const_apply ..)]; simp
             rw [← B.tsupport_eq] at q; filter_upwards [((clock_cont.tendsto v).eventually (notMem_tsupport_iff_eventuallyEq.mp q))] with y hy; rw [PinSideRT,show B (time y)=0 from hy]; simp
 by_cases q:i=timeAxis
 · filter_upwards [((clock_cont.tendsto v).eventually (shutterPRt B _ p))] with y hy; rw [αWarmRt,if_pos q]; change ((shutterXRt B (time y)*_ :ℝ):ℂ)=0; rw [show shutterXRt B (time y)=0 from hy,zero_mul]; simp
 rw[αWarmRt,if_neg q]; exact EventuallyEq.rfl
#print axioms BornUnderRT
end YM.NSF.Boundary
end

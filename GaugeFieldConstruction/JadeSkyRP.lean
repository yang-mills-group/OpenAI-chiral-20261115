import GaugeFieldConstruction.ArtHullRP
import GaugeFieldConstruction.HighCliffsRP
/-! continuous extension of Fast vertical strokes. For arbitrary Schwartz, not compact convention. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Function Mink Set Filter MeasureTheory Analysis Distribution LD Bid Work.C22 Work.C23 Work.C24 OS Small Complex
open scoped BigOperators Topology ContDiff InnerProductSpace NNReal
variable {n m:ℕ}{G:Gauge}{L:Register G}{S T:Table L}{C:LRoom T timeAxis}
variable {B:Small S C}{p q:ℝ≥0}{F:Waves S}{K:Spins S}{W:Surface S}{J:StarOp S}{D:∀ i,Blanket i}{R:S.Rotation}{s:S.RealSpin}
variable (d:PredictionL W F K J B R s){X:W.Aurora D}(H:X.FullBody F)(b: Hull B F J)
variable (v:Fin n→ Letter S)(w:Fin m→ Letter S)
lemma PtMapRP (x:Points n)(y:Points m): inner ℂ (PtVectorRP d v x) (PtVectorRP d w y)= W.W _ (bothT (Prod.fst ∘ v) (Prod.fst ∘ w) J) (bothTest (forwardRP v x) (forwardRP w y) J):=by
 unfold PtVectorRP; rw [d.assign,d.assign,(B.bowls d.link).out.at_pair,← nKernelRP]; rfl
lemma PtKernelRP :Continuous (fun x:Points n × Points m=> inner ℂ (PtVectorRP d v x.1) (PtVectorRP d w x.2)):=by
 simp_rw [PtMapRP]
 exact (W.W (n+m) (bothT (Prod.fst ∘ v) (Prod.fst ∘ w) J)).continuous.comp (bothTestMoveRP ..)
lemma CoreContRP (X:Hilbert)(M:Points n→ X)(H:Continuous (fun p:Points n×Points n=> inner ℂ (M p.1) (M p.2))):Continuous M:=by
 apply continuous_iff_continuousAt.2; intro x
 have h(i j: Points n→ Points n)(hi:Continuous i)(hj:Continuous j): Continuous (fun x=> inner ℂ (M (i x)) (M (j x))):= H.comp (hi.prodMk hj)
 have hu:Continuous (fun y=> inner ℂ (M y-M x) (M y-M x)):=by
    simp_rw [inner_sub_left,inner_sub_right]; exact ((h _ _ continuous_id continuous_id).sub (h _ (fun _=>x) continuous_id continuous_const)).sub ((h (fun _=>x) _ continuous_const continuous_id).sub continuous_const)
 have hm:Continuous (fun y=>‖M y-M x‖):=by
    simp_rw [@norm_eq_sqrt_re_inner ℂ]; exact Real.continuous_sqrt.comp (continuous_re.comp hu)
 apply Metric.continuousAt_iff.mpr
 intro p t; have he: Tendsto (fun y=> ‖M y-M x‖) (𝓝 x) (𝓝 0):= by simpa using hm.tendsto x
 obtain ⟨r,e,h⟩:= Metric.mem_nhds_iff.mp (he.eventually (gt_mem_nhds t))
 refine ⟨r,e,?_⟩; intro a q; rw [dist_eq_norm]; exact h (Metric.mem_ball.mpr q)

lemma PtContRP: Continuous (PtVectorRP d v):= CoreContRP _ _ (PtKernelRP d v v)
-- movement all complex slopes
variable {a:Heights n}(e:a∈ positiveHeight n)
local notation3 "CUPΛ"=> ({z:ℂ|0≤z.im}: Set ℂ)
local notation3 "HUPΛ"=> ({z:ℂ|0<z.im}: Set ℂ)
local notation3 "ΛRe"=> ({z:ℂ|0=z.im}: Set ℂ)
def skyPadRP (w:ℂ):ℝ≥0:= if h:0<w.im then (PadsRP (w.im • a) (HeightPlusRP e h)).choose else 0
def SkyRP (w:ℂ):= if 0<w.im then CanvasRP B v a (skyPadRP e w) w else PtVectorRP d v (w.re • dawn a)
lemma ampleWorldRP {z:ℂ}(u:z∈ HUPΛ):Small.ample (skyPadRP e z) (z.im • a):=by unfold skyPadRP; rw [dif_pos (show 0<z.im from u)]; exact (PadsRP (z.im • a) (HeightPlusRP e u)).choose_spec
lemma WeltRP (t:ℝ): SkyRP d v e t= PtVectorRP d v (t • dawn a):=by simp [SkyRP]
include H b
lemma GlorySkyRP : AnalyticOnNhd ℂ (SkyRP d v e) HUPΛ:=by
 have h : IsOpen HUPΛ:=isOpen_lt continuous_const continuous_im
 apply DifferentiableOn.analyticOnNhd _ h; intro z t; let p:=skyPadRP e z; have ht:=ampleWorldRP e t
 have hz:= BluffFrontRP B v p ht
 apply DifferentiableAt.differentiableWithinAt; apply hz.congr_of_eventuallyEq
 filter_upwards [h.mem_nhds t,((continuous_im.smul (continuous_const (y:=a))).tendsto z).eventually (HeightLateRP ht)] with zΩ kΩ m
 have hζ: 0 < im zΩ := kΩ
 unfold SkyRP; rw [if_pos hζ]
 exact eqCapRP B (forwardRP v (zΩ.re • dawn a)) d.inlet H b (ampleWorldRP e hζ) m
lemma SideSkyRP:ContinuousOn (SkyRP d v e) CUPΛ:=by
 intro x h; rcases (show 0 ≤ x.im from h).lt_or_eq with k|k
 · exact ((GlorySkyRP d H b v e x k).continuousAt).continuousWithinAt
 change Tendsto _ _ _; have hh:x∈ ΛRe:=k
 rw [show CUPΛ=HUPΛ ∪ ΛRe from Set.ext fun z=> show 0 ≤ z.im ↔ _ from le_iff_lt_or_eq,nhdsWithin_union,tendsto_sup]; refine ⟨?_,?_⟩
 · have hn:x∈closure HUPΛ:=by rw[closure_setOf_lt_im]; exact h
   haveI: (𝓝[HUPΛ] x).NeBot:= mem_closure_iff_nhdsWithin_neBot.mp hn
   have hp:= (continuous_re.smul (continuous_const (y:=dawn a))).tendsto x |>.mono_left (nhdsWithin_le_nhds (s:=HUPΛ))
   have hc:Tendsto (fun z:ℂ=>z.im • a) (𝓝[HUPΛ] x) (𝓝 0):=by
      simpa only [← k,zero_smul] using ((show Continuous (fun z:ℂ=> im z • a) from continuous_im.smul continuous_const)).tendsto x |>.mono_left (nhdsWithin_le_nhds (s:=HUPΛ))
   rw [show SkyRP d v e x=PtVectorRP d v (x.re • dawn a) from if_neg (not_lt.mpr k.ge)]
   apply (PtLoadsRP d H b v (fun z:ℂ=> z.re • dawn a) (skyPadRP e) (fun z:ℂ=> z.im • a) _ hp hc (Eventually.mono (show ∀ᶠ i in 𝓝[HUPΛ] x,i∈HUPΛ from self_mem_nhdsWithin) (fun i t=> ampleWorldRP e t))).congr'
   filter_upwards [self_mem_nhdsWithin] with zΩ kΩ; exact (if_pos (show 0 < im zΩ from kΩ)).symm
 have hx:Continuous (fun w:ℂ=>PtVectorRP d v (w.re • dawn a)):= (PtContRP d v).comp (continuous_re.smul continuous_const)
 show ContinuousWithinAt _ _ _
 apply hx.continuousWithinAt.congr (fun w h=>if_neg (not_lt.mpr (show 0=w.im from h).ge)) (if_neg _) -- tune
 exact not_lt.mpr k.ge
local notation "${Y}"=> d.system.operators
include e
lemma FrostFillRP (u: ${Y}.H)(h:∀ᶠ z:ℝ in 𝓝 0, inner ℂ u (${Y}.vector (List.ofFn (forwardRP v (z • dawn a))))=0)(t:ℝ): inner ℂ u (${Y}.vector (List.ofFn (forwardRP v (t • dawn a))))=0:=by
 let P:= (⟨d.mapSpace.toLinearMap,d.isometry.scale⟩ : ${Y}.H →ₗᵢ[ℂ] C.H); let L:= innerSL ℂ (d.mapSpace u); let F(w:ℂ):= L (SkyRP d v e w)
 have ht(z:ℝ): F z=inner ℂ u (${Y}.vector (List.ofFn (forwardRP v (z • dawn a)))):=by unfold F; rw [WeltRP]; exact (LinearIsometry.inner_map_map P u _)
 have hv:EqOn F 0 CUPΛ:= SweepΛL (L.continuous.comp_continuousOn (SideSkyRP d H b v e)) (fun i t=> L.analyticAt _ |>.comp (GlorySkyRP d H b v e i t)) (h.mono fun z s=> (ht z).trans s)
 rw[← ht]; exact hv (show (t:ℂ)∈CUPΛ from by simp)
#print axioms FrostFillRP
end YM.NSF.Boundary
end

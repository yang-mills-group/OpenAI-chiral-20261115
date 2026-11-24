import GaugeFieldConstruction.BasinRP
/-! Holomorphic vector legs preheated along TIMELIKE positiveHeight rays (can shear by Lorentz after). -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Function Mink Set Filter MeasureTheory Analysis Distribution LD Bid Work.C22 Work.C23 Work.C24 OS Small Complex Metric
open scoped BigOperators Topology ContDiff InnerProductSpace NNReal
variable {n m:ℕ}{G:Gauge}{L:Register G}{S T:Table L}{C:LRoom T timeAxis}
-- dominance via Cauchy prevents needing measurability hypothesis on derivatives.
lemma analyticPadRP {D:Hilbert} (F:ℂ→ Points n→ D){z:ℂ}{R:ℝ}(p:0<R)(g:Points n→ℝ)(hq:Integrable g)
   (hf:∀ w∈ ball z R, AEStronglyMeasurable (F w)) (h:∀ w∈ball z R,∀ x, ‖F w x‖≤g x)
   (e:∀ w∈ball z R,∀ x, DifferentiableAt ℂ (fun t=>F t x) w): DifferentiableAt ℂ (fun w=>∫ x, F w x) z:=by
 let M(w:ℂ)(x:Points n):= deriv (fun t=>F t x) w; let Q:=ball z R; let r:=R/3; let E:=ball z r
 have hr:0<r:=by unfold r; positivity
 have hE:E⊆Q:=ball_subset_ball (by unfold r; linarith)
 have hu:Q∈𝓝 z:=ball_mem_nhds z p; have hz:z∈Q:=mem_ball_self p
 have hi: Integrable (F z):= hq.mono' (hf z hz) (ae_of_all _ (h z hz))
 have hm:AEStronglyMeasurable (M z):=by
    classical
    let W(w:ℂ)(x:Points n):D:= if w∈Q then slope (fun t=>F t x) z w else 0
    refine aestronglyMeasurable_of_tendsto_ae (𝓝[≠] z) (f:=W) (fun w=>?_) (ae_of_all _ fun x=>?_)
    · by_cases k:w∈Q
      · simp only [W,if_pos k,slope_def_module]; exact ((hf _ k).sub (hf z hz)).const_smul _
      simp only [W,if_neg k]; exact aestronglyMeasurable_const
    apply ((e z hz x).hasDerivAt.tendsto_slope).congr'; filter_upwards [Eventually.filter_mono (p:=fun x=> x∈Q) (nhdsWithin_le_nhds (s:={z}ᶜ)) hu] with w hw
    exact (if_pos hw).symm
 have hs(w)(k:w∈ E)(x:Points n): ‖M w x‖≤(r)⁻¹*g x:=by
    have he:closedBall w r⊆Q:=by
       intro y t; have hz:= dist_triangle y w z; have hp:= mem_closedBall.mp t; have hq:=mem_ball.mp k
       change dist y z<R; dsimp only [r] at *; linarith
    rw [mul_comm, ← div_eq_mul_inv]; refine norm_deriv_le_of_forall_mem_sphere_norm_le hr ⟨fun i t=>(e i (he (ball_subset_closedBall t)) _).differentiableWithinAt,fun i t => (e i (he (closure_ball_subset_closedBall t)) _).continuousAt.continuousWithinAt⟩ (fun y v=> h y (he (sphere_subset_closedBall v)) x)
 exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=E) (x₀:=z) (μ:=volume) (ball_mem_nhds _ hr) (Eventually.mono (show ∀ᶠ z' in 𝓝 z, z'∈Q from hu) hf) hi hm (bound:=fun i=> (r)⁻¹*g i) (Eventually.of_forall fun x p t=> hs p t x) (hq.const_mul _) (Eventually.of_forall fun x p t=> (e p (hE t) x).hasDerivAt)).2.differentiableAt
variable (B:Small S C){p q:ℝ≥0}(v:Fin n→Letter S)(a:Heights n)
def ShadowPadRP (w:ℂ)(x:Points n):Points n:= x+w.re • dawn a
lemma traceShadowRP (w:ℂ)(x:Points n): trace (ShadowPadRP a w x)= trace x:=by ext1 i; simp [ShadowPadRP,dawn,trace,place]
def wavePadRP (x:Points n)(w:ℂ):Times n:= fun i=> ↑(YM.time (x i))+ w*↑(a i)
lemma shiftShadowRP (w:ℂ)(x:Points n):shift (ShadowPadRP a w x) (w.im • a)= wavePadRP a x w:=by
 ext1 i; unfold wavePadRP shift; apply Complex.ext<;>simp [ShadowPadRP,dawn,place]
lemma imagShadowRP (w:ℂ)(x:Points n): (fun i=> (wavePadRP a x w i).im)= w.im • a:=by ext i; simp [wavePadRP]
variable (p':ℝ≥0)
def CanvasRP (w:ℂ):= capRP B (forwardRP v (w.re • dawn a)) p' (w.im • a)
def CanvaUnitRP (w:ℂ)(x:Points n):= (Joint.materialize n (Prod.snd∘ v) x) • B.shot p' n (Prod.fst ∘ v) (w.im • a) (ShadowPadRP a w x)
lemma CanvasBudgetRP (w:ℂ): CanvasRP B v a p' w=∫ x, CanvaUnitRP B v a p' w x:=by
 unfold CanvasRP capRP CanvaUnitRP; rw[← integral_add_right_eq_self _ (w.re • dawn a)]; apply integral_congr_ae; filter_upwards with i
 have h: Prod.fst∘ forwardRP v (w.re • dawn a)=Prod.fst ∘ v:= rfl; simp [h,forwardRP,ShadowPadRP]
variable {a}
lemma ShotFrontRP {z:ℂ}(x:Points n)(u:Small.ample p' (z.im • a)): DifferentiableAt ℂ (fun t=> B.shot p' n (Prod.fst ∘ v) (t.im • a) (ShadowPadRP a t x)) z:=by
 simp_rw[fromPoint,traceShadowRP,shiftShadowRP]
 refine fromDiff B p' 0 _ (fun _=>0) _ 0 _ z ?_ ?_ (differentiableAt_const _)
 · rw [imagShadowRP]; exact ample_room u
 intro i; unfold wavePadRP; fun_prop
lemma BluffFrontRP {z:ℂ}(u:Small.ample p' (z.im • a)): DifferentiableAt ℂ (CanvasRP B v a p') z:=by
 let W:=CanvasRP B v a p'; let F:=CanvaUnitRP B v a p'
 let M:= Joint.materialize n (Prod.snd ∘ v); let J:=(∏ i, ‖B.bar p' (v i).1‖)*‖C.omega‖
 obtain ⟨r,hr,hR⟩:=Metric.mem_nhds_iff.mp ((show Continuous (fun w:ℂ=>w.im • a) from continuous_im.smul continuous_const).tendsto z |>.eventually (HeightLateRP u))
 rw [show CanvasRP B v a p'= fun w=>∫ x:Points n, F w x from funext fun i=> CanvasBudgetRP B v a p' i]; apply analyticPadRP (D:=C.H) F hr (fun i=> ‖M i‖ * J) (M.integrable.norm.mul_const J)
 · intro w t; have hx : Continuous (F w) := M.continuous.smul ((shot_control B p' n (Prod.fst∘v) _ (hR t)).1.comp (continuous_id.add (continuous_const (y:=w.re • dawn a)))) -- check
   exact hx.aestronglyMeasurable
 · intro w t x; change ‖M x • _‖ ≤ _; rw [norm_smul]; exact mul_le_mul_of_nonneg_left ((shot_control B p' _ (Prod.fst ∘ v) _ (hR t)).2 _) (norm_nonneg _)
 intro w t x; exact (ShotFrontRP B v p' x (hR t)).const_smul _
#print axioms BluffFrontRP
end YM.NSF.Boundary
end

import YM.SU5.Registration.LineUp.Diversion
import YM.Work.C07
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
-- possibly build Pin? check
/-!
 # Ward test smoothing for the presently only C0 Eu estimates. Keep proper rotation law.
 price cut-offs at positive clearance & compact `foldE` support. maintain EXACT
 Eu orientations while passing with smooth approximations. not assuming spatial derivatives at pre-spectrum-socket.
 see also YM/Work/C07.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed
open Boundary Mink Function Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff Convolution BigOperators InnerProductSpace
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
namespace HelioRoof

local notation "E" => Points n
-- positive radius bump at squared norm
def coal (r:ℝ)(hr:0<r): ContDiffBump (0:ℝ) := ⟨r^2/2,r^2,by positivity,half_lt_self (by positivity)⟩
def lily (r:ℝ)(hr:0<r)(x:Points n):= coal r hr (‖x‖^2) -- Lean parser exponent!
variable {r:ℝ}(hr:0<r)
lemma lily_def (x:E) : lily r hr x= coal r hr (inner ℝ x x):=by rw [lily,real_inner_self_eq_norm_sq]
lemma lily_support : support (lily (n:=n) r hr)⊆ ball 0 r:=by
 intro x hx; have he: ‖x‖^2∈support (coal r hr):= hx; rw [(coal r hr).support_eq, mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at he; rw [mem_ball, dist_zero_right]; exact lt_of_pow_lt_pow_left₀ 2 hr.le he -- tune
lemma lily_smooth : ContDiff ℝ ∞ (lily (n:=n) r hr):=by
 simp_rw [funext (lily_def (n:=n) hr)]; apply (coal r hr).contDiff.comp ((contDiff_id (𝕜:=ℝ)).inner ℝ contDiff_id)
lemma lily_compact : HasCompactSupport (lily (n:=n) r hr):=(isCompact_closedBall (0:E) r).of_isClosed_subset (isClosed_tsupport _) (closure_minimal ((lily_support hr).trans ball_subset_closedBall) isClosed_closedBall)
noncomputable def Qmass (n:ℕ) : ℝ:= ∫ x:Points n,lily r hr x -- r implicit argument order? (n then HR?)
lemma pos_total : 0 < Qmass hr n:= integral_pos_of_integrable_nonneg_nonzero (lily_smooth hr).continuous ((lily_smooth hr).continuous.integrable_of_hasCompactSupport (lily_compact hr)) (fun i=>(coal r hr).nonneg) (x:=(0:E)) (by rw [lily,norm_zero,zero_pow (by decide),(coal _ _).one_of_mem_closedBall (mem_closedBall_self (coal r hr).rIn_pos.le)]; exact one_ne_zero)
noncomputable def localSpend (x:E) := (Qmass hr n)⁻¹ * lily r hr x
lemma spend_full : ∫ x, localSpend hr (x:E) = 1:=by unfold localSpend; rw [integral_const_mul]; exact inv_mul_cancel₀ (pos_total (n:=n) hr).ne'
lemma spend_pos (x:E) : 0 ≤ localSpend hr x:=mul_nonneg (inv_nonneg.mpr (pos_total hr).le) ((coal r hr).nonneg' _)
lemma spend_smooth : ContDiff ℝ ∞ (localSpend (n:=n) hr):=contDiff_const.mul (lily_smooth hr)
lemma spend_support : support (localSpend (n:=n) hr)⊆ ball 0 r:= (support_mul_subset_right (fun _:E=> (Qmass hr n)⁻¹) _).trans (lily_support hr) -- tune
lemma spend_compact : HasCompactSupport (localSpend (n:=n) hr):= (lily_compact hr).mul_left -- method?
lemma spend_frame (U:Frames n)(x:E) : localSpend hr (reFrame U x)=localSpend hr x:=by unfold localSpend lily; rw [(show ‖reFrame U x‖=_ from (podium U).norm_map x)]
-- convolution with these costs. Orientation even at finite r. Neg-Haar.
def inked (K: E→ℂ):= ((localSpend hr) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] K : E→ℂ) -- HR argument u
private theorem negInvariant (n:ℕ) : (volume : Measure (Points n)).IsNegInvariant := ⟨(LinearIsometryEquiv.neg ℝ : Points n ≃ₗᵢ[ℝ] Points n).measurePreserving.map_eq⟩
lemma inked_smooth {K:E→ℂ}(h:Continuous K) : ContDiff ℝ ∞ (inked hr K):= by letI:=negInvariant n; exact (spend_compact hr).contDiff_convolution_left _ (spend_smooth hr) h.locallyIntegrable
lemma inked_exists {K:E→ℂ}(h:Continuous K)(x:E): Integrable (fun v:E=> (localSpend hr v) • K (x-v)):= by
 apply (Continuous.smul (spend_smooth hr).continuous (h.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport; exact (spend_compact hr).smul_right -- which?
lemma inked_frame (U:Frames n)(K K': E→ℂ) (p:∀ x,K' (reFrame U x)=K x)(x:E) : inked hr K' (reFrame U x)=inked hr K x:=by
 unfold inked; rw [convolution_def,← (podium U).measurePreserving.integral_comp (podium U).toHomeomorph.measurableEmbedding]; change (∫ y:E, localSpend hr (reFrame U y) • K' (reFrame U x-reFrame U y))= _; simp_rw [show ∀ u:E,reFrame U x-reFrame U u=reFrame U (x-u) from fun i=>(map_sub (podium U) x i).symm,spend_frame hr,p]; rfl
-- variable widths shape. require shrink for label actors. apply simultaneously to actual folds via moving positions.
omit hr
lemma local_spends {I:Type*} (r:I→ℝ)(h:∀ i,0<r i)(V':Filter I)(t:Tendsto r V' (𝓝 0)) : Tendsto (fun i=> Function.support (localSpend (n:=n) (h i))) V' (𝓝 0).smallSets:=by
 refine tendsto_smallSets_iff.mpr (fun s v=>?_); obtain ⟨R,p,d⟩:= Metric.mem_nhds_iff.mp v; filter_upwards [t.eventually (gt_mem_nhds p)] with i hi; exact (spend_support (h i)).trans ((ball_subset_ball hi.le).trans d)
lemma inked_bought {I:Type*} (r:I→ℝ)(h:∀ i,0<r i)(V':Filter I)(t:Tendsto r V' (𝓝 0))(f:I→E) {x:E}(p:Tendsto f V' (𝓝 x)) {K:E→ℂ}(hK: Continuous K) : Tendsto (fun i=> inked (h i) K (f i)) V' (𝓝 (K x)):= by
 exact convolution_tendsto_right (Eventually.of_forall fun i=>spend_pos (n:=n) (h i)) (Eventually.of_forall fun i=>spend_full (n:=n) (h i)) (local_spends r h _ t) (Eventually.of_forall (p:=fun _=> AEStronglyMeasurable K volume) (fun i=>hK.aestronglyMeasurable)) ((hK.tendsto x).comp tendsto_snd) p

-- cut all collisions (even at clearance without any one-axis painting order). use continuous cutoff, needn't smooth until later.
def facePair (r:ℝ)(x:E)(i j:Fin n):ℝ:= if i=j then 1 else max 0 (min 1 (dist (x i) (x j)/r-1))
noncomputable def faceRoof (r:ℝ)(x:E) := ∏ i:Fin n,∏ j:Fin n,facePair r x i j
lemma drop_face {r:ℝ}(hr:0<r)(x:E)(i j:Fin n)(h:i≠j)(p:dist (x i) (x j) ≤ r): faceRoof r x=0:= by
 let he:= (div_le_one hr).mpr p; apply Finset.prod_eq_zero (Finset.mem_univ i); apply Finset.prod_eq_zero (Finset.mem_univ j); rw [facePair,if_neg h,max_eq_left]; exact le_trans (min_le_right _ _) (sub_nonpos.mpr he)
include hr
lemma roof_zero (x:E)(v:x∉conf n): faceRoof r =ᶠ[𝓝 x] fun _=> (0:ℝ):=by
 obtain ⟨i,j,h,t⟩: ∃ i j:Fin n,x i=x j ∧ i≠ j:= by
   unfold conf at v; simp only [Set.mem_setOf_eq,Injective] at v; push Not at v; exact v
 have he:Continuous (fun x:E=> dist (x i) (x j)):=by fun_prop
 refine ((he.tendsto x).eventually (gt_mem_nhds (show dist (x i) (x j) < r by rwa [h,dist_self]))).mono (fun y hy=> drop_face hr y i j t hy.le)
 -- goals
omit hr
lemma roof_cont (r:ℝ): Continuous (faceRoof (n:=n) r):= by
 unfold faceRoof; refine continuous_finsetProd _ fun i _=> continuous_finsetProd _ fun j _=>?_; by_cases h:i=j <;> simp [facePair,h] <;> try fun_prop
lemma roof_turn (r:ℝ)(x:E)(U:Ortho): faceRoof r (Points.move U x)=faceRoof r x:= by
 have hf i j: dist (Points.move U x i) (Points.move U x j)=dist (x i) (x j):= (U.motion).dist_map _ _; simp_rw[faceRoof,facePair,hf]
lemma roof_enough {K: Set E}(hK:IsCompact K)(p:K ⊆ conf n) : ∀ᶠ r:ℝ in 𝓝[>] 0, ∀ x∈K, faceRoof r x=1:=by
 have C (i j: Fin n) (e:i≠j) : ∀ᶠ r:ℝ in 𝓝 0, ∀ y∈K, 2*r ≤ dist (y i) (y j):=by
    refine hK.eventually_forall_of_forall_eventually (fun y hy=>?_); have h:Continuous (fun x:ℝ × E => dist (x.2 i) (x.2 j)-2*x.1):=by fun_prop
    refine ((h.tendsto (0,y)).eventually (le_mem_nhds ?_)).mono (fun z hz=> sub_nonneg.mp hz); simp only [mul_zero,sub_zero]; exact (dist_pos.mpr ((show Injective y.ofLp from p hy).ne e))
 have h:∀ᶠ r:ℝ in 𝓝 0, ∀ i j, i≠j → ∀ y∈K, 2*r ≤ dist (y i) (y j) := by simp only [eventually_all]; exact C
 filter_upwards [h.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with r H hr x hx; unfold faceRoof; refine Finset.prod_eq_one fun i _=> Finset.prod_eq_one fun j _=>?_; unfold facePair; split; · rfl
 next e=> rw [min_eq_left,max_eq_right zero_le_one]; exact le_sub_iff_add_le.mpr ((le_div_iff₀ (mem_Ioi.mp hr)).mpr (by rw [one_add_one_eq_two]; exact H i j e x hx))
variable {R:Courts V}{F:InkWaves V}(p:R.Carriage F)(t:F.Region)
include hr
noncomputable def awning (r:ℝ) (R:Courts V)(F:InkWaves V): EuLeaflet V:= fun n x=> (faceRoof r x : ℂ) • helio R F n x
noncomputable def canvas (v:Fin n→V)(R:Courts V)(F:InkWaves V)(d:ℝ):= inked hr (fun x=> awning d R F n x v)
-- not claiming permutation but only rotations for approximate Ward. EXACT even unregistered tiny ties. 
include p t
omit hr in
lemma awning_turn (x:E)(U:Ortho)(h:Lorentz.properTurn U)(v:Fin n→V)(d:ℝ): awning d R F n (Points.move U x) (R.eu U ∘ v)=awning d R F n x v:=by
 have he: (helio R F n (Points.move U x)) (R.eu U ∘ v)=helio R F n x v:= helio_carries p t (U,1) h x v; unfold awning; rw [roof_turn]; exact congrArg ((faceRoof d x : ℂ) • ·) he
lemma awning_cont (v:Fin n→V) : Continuous (fun x=> awning r R F n x v):=by
 refine continuous_iff_continuousAt.mpr (fun x=>?_); by_cases h:x∈conf n
 · exact (Complex.continuous_ofReal.continuousAt.comp ((roof_cont r).continuousAt (x:=x))).smul (((helio_cont p t v) _ h).continuousAt ((conf_open n).mem_nhds h))
 exact (show ContinuousAt (fun _:E=> (0:ℂ)) x from continuousAt_const).congr_of_eventuallyEq ((roof_zero hr x h).mono (fun y hy=>by dsimp only [awning]; rw [hy]; simp))
lemma canvas_smooth (v:Fin n→V)(d:ℝ)(h:0<d) : ContDiff ℝ ∞ (canvas hr v R F d):=inked_smooth hr (awning_cont h p t v)
lemma canvas_turn (v:Fin n→V)(d:ℝ)(x:E)(U:Ortho)(u:Lorentz.properTurn U) : canvas hr (R.eu U ∘ v) R F d (Points.move U x)= canvas hr v R F d x:= inked_frame hr (U,1) _ _ (fun y=>awning_turn p t y U u v d) x -- maybe defeq
-- produce smooth approximation multilinear. integrate
noncomputable def pigment (d:ℝ)(h:0<d): EuLeaflet V:= by
 refine fun n x=> { toFun:=fun v=>canvas hr v R F d x, map_update_add':=fun m i a b=>?_, map_update_smul':=fun m i c x'=>?_ }
 · unfold canvas inked; simp_rw [convolution_def, MultilinearMap.map_update_add, map_add]; apply integral_add <;> exact inked_exists hr (awning_cont h p t _) x
 unfold canvas inked; simp_rw [convolution_def, MultilinearMap.map_update_smul]; rw [← integral_smul]; apply integral_congr_ae; filter_upwards with w; exact smul_comm (localSpend hr w) c ((awning d R F n (x-w)) (update m i x'))
 -- type includes proof p etc. budget
lemma pigment_is (v:Fin n→V)(d:ℝ)(h:0<d)(x:E) : pigment hr p t d h n x v=inked hr (fun x=>awning d R F n x v) x:=rfl
lemma pigment_turn (x:E)(U:Ortho)(h:Lorentz.properTurn U)(v:Fin n→V)(d:ℝ)(w:0<d): pigment hr p t d w n (Points.move U x) (R.eu U ∘ v)=pigment hr p t d w n x v:=canvas_turn hr p t v d x U h
lemma pigment_smooth (v:Fin n→V)(d:ℝ)(u:0<d): ContDiff ℝ ∞ (fun x=> pigment hr p t d u n x v) := canvas_smooth hr p t v d u
omit hr
-- convergence as r→0 for fixed conf cutoff. Uniform on compact via varying positions (below). doesn't assert jointly →0 crossing changing d also.
lemma pigment_gain {I:Type*} (r:I→ℝ)(h:∀ i,0<r i)(V':Filter I)(t':Tendsto r V' (𝓝 0))(f:I→E) {x:E}(e:Tendsto f V' (𝓝 x)) (d:ℝ)(w:0<d)(v:Fin n→V): Tendsto (fun i=> pigment (h i) p t d w n (f i) v) V' (𝓝 (awning d R F n x v)):= inked_bought r h V' t' f e (awning_cont w p t v)

end HelioRoof
end YM.SatinWFixed
open YM.SatinWFixed HelioRoof
#print axioms pigment_gain
#print axioms pigment_turn
#print axioms pigment_smooth

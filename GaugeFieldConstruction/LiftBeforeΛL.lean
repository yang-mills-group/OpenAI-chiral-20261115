import GaugeFieldConstruction.EmitBeforeΛL
/-!
 # Analytic direction sweep *arbitrary* joint Mink kernel in this contour, compact tests translated in abs.P.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Function Filter Set Mink MeasureTheory Analysis Kernel Complex Metric Distribution
open scoped BigOperators Topology ContDiff InnerProductSpace
open Complex
variable {n:ℕ}
variable {G:Gauge}{L:Register G}{S:Table L}{Y:Surface S}{D:∀ i,Blanket i}{F:Waves S}{A:Y.Aurora D}(e:A.FullBody F)
variable (D':Blanket n)(X:Distn (Points n))(f:Joint n) (h:HasCompactSupport (f:Points n→ℂ))
local notation3 "CUPΛ"=> ({z:ℂ|0≤z.im}: Set ℂ)
local notation3 "HUPΛ"=> ({z:ℂ|0<z.im}: Set ℂ)
def HullWrapΛL (v x:Points n)(z:ℂ): Full n:= glow (x+ z.re • v) (z.im • v)
lemma GlowHullΛL (v x:Points n)(z:ℂ): HullWrapΛL v x z=penΛ n x+ z • penΛ n v:=by
 ext1 i; change _= glow _ (0:Points n) i+ z*glow _ (0:Points n) i
 simp only [HullWrapΛL,glow,map_add,map_smul,map_zero,PiLp.add_apply,PiLp.smul_apply] -- tune
 apply Complex.ext<;> simp [smul_eq_mul,mul_comm]
abbrev HullAheadΛL(v:Points n) (z:ℂ):Joint n:=Probe.ahead (z.re • v) f
lemma HullContΛL (v:Points n):Continuous (HullAheadΛL f v):=by
 have h:= Work.C08.continuous_affine_probe (fun z:ℂ=> z.re • v) (fun _=> ContinuousLinearEquiv.refl ℝ (Points n)) f (continuous_re.smul continuous_const) continuous_const continuous_const
 refine h.congr fun x=>?_ ; ext; simp [HullAheadΛL]
def LiftBeforeΛL (v:Points n)(z:ℂ):ℂ:= D'.partialD X (z.im • v) (HullAheadΛL f v z)
variable {v:Points n}(hv:v∈fields n)(V:Fin n→ S.Union)
include hv
lemma VBefΛL:ContinuousOn (LiftBeforeΛL D' X f v) CUPΛ:=by
 intro z h
 have ht(y:ℂ)(p:y∈CUPΛ): y.im • v∈shores n:=by
    rcases eq_or_lt_of_le (show 0≤y.im from p) with a|a
    · rw[←a,zero_smul]; exact flat n
    exact warmer n (upStretchΛL hv _ a)
 have hc:Continuous (fun z:ℂ=>z.im • v):=continuous_im.smul continuous_const
 exact partialJΛL D' _ _ _ _ _ (ht z h) ((HullContΛL f v).continuousWithinAt) (hc.continuousWithinAt.tendsto_nhdsWithin (fun z=>ht z))
include e
lemma ΦPriceΛL (z:ℂ)(hx:z∈HUPΛ): LiftBeforeΛL (D n) (Y.W n V) f v z=∫ x,A.emit V (HullWrapΛL v x z)*f x:=by
 unfold LiftBeforeΛL; rw [e.builds _ _ _ (upStretchΛL hv _ (show 0<z.im from hx)), ← integral_add_right_eq_self _ (z.re • v)]; apply integral_congr_ae; filter_upwards with i; simp [HullAheadΛL,HullWrapΛL]
include h
lemma analyticBeforeΛL : AnalyticOnNhd ℂ (LiftBeforeΛL (D n) (Y.W n V) f v) HUPΛ:=by
 let T:(ℂ×Points n)→Full n:=fun z=> HullWrapΛL v z.2 z.1
 let X:= A.emit V; let P:=Set.univ (α:=Points n); let M:= HUPΛ
 let Q(z:ℂ)(i:Points n):= X (T (z,i))*f i; let B(z:ℂ)(i:Points n):= fderiv ℂ X (T (z,i)) (penΛ n v)*f i; let J(z:ℂ):=∫ i:Points n,Q z i
 let C:=tsupport f
 have w : IsOpen M:= isOpen_lt continuous_const continuous_im
 have hT:Continuous T:=by unfold T; simp_rw [GlowHullΛL]; fun_prop
 have ht(z:ℂ×Points n)(t:z.1∈M):T z∈tube n:= roseΛ (upStretchΛL hv z.1.im t) _
 have hA:AnalyticOnNhd ℂ X (tube n):=e.hol n _
 have he(z:ℂ×Points n)(t:z.1∈M): ContinuousAt (uncurry Q) z ∧ ContinuousAt (uncurry B) z := by
    have u:=ht z t; have hi:ContinuousAt _ z:= f.continuous.continuousAt.comp (f:=Prod.snd) (continuousAt_snd (p:=z)) -- tune
    exact ⟨(((hA _ u).continuousAt.comp (f:=T) hT.continuousAt).mul hi), ((((hA _ u).fderiv.continuousAt.comp (f:=T) hT.continuousAt).clm_apply continuousAt_const).mul hi)⟩
 have hs(z:ℂ)(t:z∈M): Integrable (Q z) ∧ AEStronglyMeasurable (B z):= by
    let U(x:Points n):=(z,x); have hz:Continuous U:= continuous_const.prodMk continuous_id
    exact ⟨(continuous_iff_continuousAt.mpr fun i=> (he (U i) t).1.comp (f:=U) hz.continuousAt).integrable_of_hasCompactSupport (μ:=volume) h.mul_left,(continuous_iff_continuousAt.mpr fun i=> (he (U i) t).2.comp (f:=U) hz.continuousAt).aestronglyMeasurable⟩ -- tune typo
 have hZ(z:ℂ)(t:z∈M)(x:Points n): HasDerivAt (fun p=> Q p x) (B z x) z:=by
    have u:HasDerivAt (fun p=> T (p,x)) (penΛ n v) z:=by unfold T; simp_rw [GlowHullΛL]; exact ((hasDerivAt_const z _).add ((hasDerivAt_id' z).smul_const _)).congr_deriv (by simp)
    exact ((((hA _ (ht _ t)).differentiableAt.hasFDerivAt).comp_hasDerivAt z u).mul_const _)
 have hz:DifferentiableOn ℂ J M :=by
    intro z t; obtain ⟨r,u,hr⟩:= Metric.mem_nhds_iff.mp (w.mem_nhds t); let Z:= Metric.closedBall z (r/2); have hK: Z⊆M:=(Metric.closedBall_subset_ball (half_lt_self u)).trans hr
    have hu: IsCompact (Z ×ˢ C):= (isCompact_closedBall _ _).prod h; obtain ⟨s,hs'⟩:= hu.bddAbove_image (f:=fun z=> ‖uncurry B z‖) (fun z p=> (he z (hK p.1)).2.norm.continuousWithinAt)
    have hi:= (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=Z) (x₀:=z) (μ:=volume) (Metric.closedBall_mem_nhds _ (half_pos u)) (Eventually.mono (w.mem_nhds t) (fun z (p:z∈M)=> (hs _ p).1.aestronglyMeasurable)) (hs _ t).1 (hs _ t).2 (bound:=C.indicator (fun _=>s)) ?_ ?_ (Eventually.of_forall fun x p hp=> hZ p (hK hp) x)).2; -- maybe syntactic
    · exact hi.differentiableAt.differentiableWithinAt
    · refine Eventually.of_forall fun x p e=>?_
      by_cases m:x∈C
      · rw [indicator_of_mem m]; exact hs' ⟨(p,x),⟨e,m⟩,rfl⟩
      rw [indicator_of_notMem m]; unfold B; rw [image_eq_zero_of_notMem_tsupport m, mul_zero,norm_zero]
    exact (integrable_indicator_iff (isClosed_tsupport _).measurableSet).mpr (integrableOn_const (show volume C≠⊤ from h.measure_lt_top.ne))
 apply DifferentiableOn.analyticOnNhd _ w; exact hz.congr (fun p hp=> ΦPriceΛL e f hv V p hp)
#print axioms analyticBeforeΛL
end YM.NSF.Boundary
end

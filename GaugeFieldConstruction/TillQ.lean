import GaugeFieldConstruction.Beldam
/- Pulling cap derivatives at first Gauge U -/
set_option autoImplicit false
set_option maxHeartbeats 110000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Precision Finset MeasureTheory Gauge RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.Frobenius Classical
open Push.Uniform Buffered.Region FlightFlux Work Tensor
variable {E F D:Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup D][NormedSpace ℝ D] {K d v t r u c:ℝ}{j k:ℕ}{n:Side}{G:Gauge}
namespace Shield
open F03
variable (U:Config G n){L:Config G n→F}{A B:Directions G n}
abbrev turnq (L:Config G n→F)(u:ℝ)(U:Config G n): Directions G n→L[ℝ] F:= fderiv ℝ (L ∘ solo u U) 0
abbrev hue_T (L:Config G n→F)(U:Config G n):= fderiv ℝ (L ∘ increment U) 0
abbrev fog (G:Gauge)(n:Side):=ContinuousLinearMap.inl ℝ (Directions G n) (Directions G n)
abbrev leg (G:Gauge)(n:Side):=ContinuousLinearMap.inr ℝ (Directions G n) (Directions G n)
private lemma single_fold (H: Directions G n → F)(p: Allows (k+1) (L ∘ βten t U) 0 c): Jet.Allows k (fun v:Directions G n=> fderiv ℝ (L ∘ βten t U) (fog G n v)) 0 c:=by
 refine comps (fog G n) ?_ ?_
 · have h: Jet.Allows (k+1) (L∘ βten t U) 0 c:= ⟨p.1.of_le le_top,p.2⟩
   rw [map_zero]; exact h.slide
 · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v=>?_ ; change ‖((v,0):tandem G n)‖≤_; simp
lemma turn_press (H:ContDiffAt ℝ ω (L ∘ βten t U) 0): turnq L t ∘ solo t U =ᶠ[𝓝 0] (fun v=> fderiv ℝ (L ∘ βten t U) (fog G n v) ∘L leg G n):=by
 let h:=H.eventually (by simp); have hh: Tendsto (fog G n) (𝓝 0) (𝓝 0):=map_zero (fog G n) ▸ (fog G n).continuous.continuousAt.tendsto
 filter_upwards [hh.eventually h] with v hv
 let Q:=L ∘ βten t U; have hp:HasFDerivAt Q (fderiv ℝ Q (fog G n v)) (fog G n v):= (hv.differentiableAt (by simp)).hasFDerivAt
 have he : HasFDerivAt (fun q: Directions G n=>(v,q)) (leg G n) 0:= (hasFDerivAt_const ..).prodMk (hasFDerivAt_id _)
 exact (hp.comp (f:=fun q:Directions G n=> (v,q)) 0 he).fderiv -- change
abbrev relInk(A:Type)[NormedAddCommGroup A][NormedSpace ℝ A](G:Gauge)(n:Side): ((tandem G n) →L[ℝ] A) →L[ℝ] ((Directions G n) →L[ℝ] A):= (ContinuousLinearMap.compL ℝ _ _ _).flip (leg G n)
private lemma cruise(A:Type)[NormedAddCommGroup A][NormedSpace ℝ A](G:Gauge)(n:Side): ‖relInk A G n‖≤1:=by
 apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro q; rw [one_mul]; apply le_trans (q.opNorm_comp_le _); apply mul_le_of_le_one_right (norm_nonneg _); exact ContinuousLinearMap.opNorm_le_bound (leg G n) zero_le_one (fun v=>by change ‖((0,v):tandem G n)‖≤_; simp)
lemma pull_turn(p: Allows (k+1) (L ∘ βten t U) 0 c): Jet.Allows k (turnq L t ∘ solo t U) 0 c:=by
 have he:= (single_fold U (fun _=> (0:F)) p).linear (relInk F G n) (cruise ..); rw [one_mul] at he; exact he.germ ((turn_press _ p.analytic).symm)
private lemma solo_1 : solo 1 U= increment U:=funext fun x=>by unfold solo; rw [one_smul]
lemma turn_1 (x:Directions G n): turnq L 1 U x=hue_T L U x:=by rw [turnq,hue_T, solo_1]
lemma turn_c (H:ContDiffAt ℝ ω (L ∘ increment U) 0) : ContDiffAt ℝ ω (hue_T L ∘ increment U) 0:=by
 let Q:= βten (1:ℝ) U; let c(L':Config G n→F) := fderiv ℝ (L' ∘ Q)
 have hh:= turn_press U (engage_A U H); have hv:hue_T L ∘ increment U =ᶠ[𝓝 0] relInk F G n ∘ (c L ∘ fog G n):=by rw [←solo_1 U, show hue_T L= turnq L 1 from funext (fun V=> Eq.symm (ContinuousLinearMap.ext (turn_1 V)))]; exact hh
 have he:ContDiffAt ℝ ω (c L ∘ fog G n) 0:= ((show ContDiffAt ℝ ω (c L) (fog G n 0) from (by rw [map_zero]; exact (engage_A U H).fderiv_right (by simp))).comp _ (fog G n).contDiff.contDiffAt)
 exact ((relInk F G n).contDiff.contDiffAt.comp _ he).congr_of_eventuallyEq hv
lemma tone_pow {A: Directions G n}(p:ContDiffAt ℝ ω (L ∘ increment U) 0): turnq L t U A=hue_T L U (t • A):=by
 let B:=t • ContinuousLinearMap.id ℝ (Directions G n); let c:=L ∘ increment U; change fderiv ℝ (L ∘ solo t U) _ _= _; rw [show L ∘ solo t U=c ∘ B from rfl, fderiv_comp _ (by rw [B.map_zero]; exact p.differentiableAt (by simp)) B.differentiableAt,B.fderiv, B.map_zero]; rfl
lemma tone_s(p:∀ z: Config G n,ContDiffAt ℝ ω (L ∘ increment z) 0): turnq L t U = t • hue_T L U:=ContinuousLinearMap.ext (fun A=> (tone_pow _ (p U)).trans ((hue_T L U).map_smul t A))
lemma turn_slope (p:ContDiffAt ℝ ω (L ∘ increment U) 0)(q:fderiv ℝ (L ∘ increment U) 0=0): fderiv ℝ (hue_T L ∘ increment U) 0 A B= iteratedFDeriv ℝ 2 (L ∘ increment U) 0 ![A,B]:=by
 let R:= relInk F G n; let X:= L ∘ βten 1 U; let c(v:Directions G n):= fderiv ℝ X (fog G n v)
 have hv:hue_T L ∘ increment U =ᶠ[𝓝 0] R ∘ c:=by
    have he:=turn_press U (engage_A U p); have hh: increment U=solo 1 U:=(solo_1 U).symm; exact (show hue_T L ∘ increment U =ᶠ[𝓝 0] turnq L 1 ∘ solo 1 U from (Filter.EventuallyEq.of_eq (by rw [hh, show hue_T L=turnq L 1 from funext fun V=> Eq.symm (ContinuousLinearMap.ext (turn_1 V))]))).trans he
 let h:= engage_A U p
 have hh: HasFDerivAt c (fderiv ℝ (fderiv ℝ X) 0 ∘L fog G n) 0 := (((map_zero (fog G n)|>.symm) ▸ ((h.fderiv_right (m:=1) (by simp)).differentiableAt (by norm_num)).hasFDerivAt) : HasFDerivAt (fderiv ℝ X) (fderiv ℝ (fderiv ℝ X) 0) (fog G n 0)).comp 0 (fog G n).hasFDerivAt
 rw [← engage_D U p q, iteratedFDeriv_two_apply,hv.fderiv_eq (𝕜:=ℝ), (R.hasFDerivAt.comp _ hh).fderiv]; rfl
end Shield
end YM.CF.XGarden
end

import YM.CF.Neige.Stop
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.ResolventVolume
set_option autoImplicit false
noncomputable section
namespace YM.CF.Neige
open Char Summit
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
variable {α E:Type} [Fintype α][DecidableEq α] [NormedAddCommGroup E][NormedSpace ℝ E] {p:α→Site c}{a:ℕ} {K v d s t:ℝ} {n:ℕ}
open Finset Filter
open AnalyticBridge.RelativeLogdet AnalyticNext.ConnectedActivity
abbrev edgeM (A:Shelf α):= ResolventVolume.graph 1 A
def tea_r (A: Shelf α)(P:ℝ→Shelf α)(t:ℝ):= 1-edgeM A t*P t
def grind(A:Shelf α)(P:ℝ→Shelf α)(n:ℕ)(t:ℝ):= A*P t * (tea_r A P t)^n
def pulseX (A:Shelf α)(P:ℝ→Shelf α)(n:ℕ):ℝ:= ∫ t in Isle,Matrix.trace (grind A P n t)
lemma ampO (A:Shelf α)(i j:α):|A i j|  ≤  ‖paintO (τ:=α) A‖:=by -- i explicit
 let v : Fish α:= Pi.single j 1; have hp: ‖v‖ ≤ 1:=(pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i=>by by_cases i=j <;> simp [*,v]
 rw [show A i j= paintO A v i from ?_]; exact ((norm_le_pi_norm (paintO A v) _).trans (((paintO A).le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg _) hp)))
 unfold v; rw [paintO_p,mulVec_single_one]; rfl
lemma op_p(A:Shelf α)(M:ℝ)(h:‖paintO (τ:=α) A‖ ≤  M)(n:ℕ): ‖paintO (τ:=α) (A^n)‖  ≤  M^n:=by
 induction n with
 | zero=> rw [pow_zero,paint_one,pow_zero]; exact ContinuousLinearMap.norm_id_le
 | succ i ih=> rw [pow_succ A,paint_mul]; exact (ContinuousLinearMap.opNorm_comp_le ..).trans ((mul_le_mul ih h (norm_nonneg _) (pow_nonneg ((norm_nonneg _).trans h) _)).trans_eq (pow_succ _ _).symm)
lemma op_trace (A B:Shelf α)(M t:ℝ)(h:‖paintO (τ:=α) A‖ ≤ M)(ht:‖paintO (τ:=α) B‖ ≤ t)(n:ℕ):|trace (A*B^n)| ≤ Fintype.card α*M*t^n:=by
 unfold trace; apply (Finset.abs_sum_le_sum_abs ..).trans; apply (sum_le_sum (g:=fun _=> M*t^n) fun i _=>?_).trans_eq
 · simp only [sum_const,card_univ,nsmul_eq_mul,mul_assoc]
 apply (ampO _ _ _).trans; rw [paint_mul]; exact (ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_mul h (op_p B t ht n) (norm_nonneg _) ((norm_nonneg _).trans h))
lemma porter (A P:Shelf α)(t:ℝ) (h:IsUnit (edgeM A t).det)(u:ℝ)
 (ht:‖paintO (τ:=α) (1-edgeM A t*P)‖ ≤ u)(hx:u<1): HasSum (fun n:ℕ=> Matrix.trace (A*P*(1-edgeM A t *P)^n)) (trace ((edgeM A t)⁻¹*A)):=by
 let D:=edgeM A t; let K:=1-D*P; let C:= (Fintype.card α:ℝ); let q(n:ℕ):=Matrix.trace (A*P*K^n)
 have hu:0 ≤ u:=(norm_nonneg _).trans ht; let T:= summable_geometric_of_lt_one hu hx; have hp:Summable q:= .of_norm_bounded (T.mul_left (C*‖paintO (τ:=α) (A*P)‖)) fun i=>op_trace _ _ _ _ le_rfl ht i
 let U:=A*D⁻¹
 have he:U*K=U-A*P:=by unfold U K; rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, ← Matrix.mul_assoc D⁻¹,Matrix.nonsing_inv_mul D h,Matrix.one_mul]
 have hh(n:ℕ): U*K^n=U-∑ i∈Finset.range n,A*P*K^i:=by
    induction n with
    | zero=> simp
    | succ i ih=> nth_rw 1 [pow_succ']; rw [← Matrix.mul_assoc,he,Matrix.sub_mul,ih,sum_range_succ]; abel
 have hZ(i): trace (U * K^i)=trace U- ∑ j∈Finset.range i,q j:=by rw [hh,trace_sub,trace_sum]
 have hh:Tendsto (fun i:ℕ=>trace (U*K^i)) atTop (𝓝 0):=tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _=>norm_nonneg _) (op_trace _ _ _ _ le_rfl ht) (by simpa using! (tendsto_pow_atTop_nhds_zero_of_lt_one hu hx).const_mul (C*‖paintO U‖)))
 simp_rw [hZ] at hh
 have hQ: Tendsto (fun i=> trace U-∑ j∈Finset.range i,q j) atTop (𝓝 (trace U-∑' j,q j)):=tendsto_const_nhds.sub hp.hasSum.tendsto_sum_nat
 rw [Matrix.trace_mul_comm,show trace _=_ from sub_eq_zero.mp (tendsto_nhds_unique hQ hh)]; exact hp.hasSum
lemma tepid(A:Shelf α)(P:ℝ→Shelf α)(h:ContinuousOn P Isle)(n:ℕ):ContinuousOn (fun t=>trace (grind A P n t)) Isle:=
 (show Continuous (fun M:Matrix α α ℝ=>trace M) from continuous_id.matrix_trace).comp_continuousOn ((continuousOn_const.mul h).mul ((continuousOn_const.sub ((ResolventVolume.graph_continuous ..).continuousOn.mul h)).pow n))
lemma hikes (A:Shelf α)(P:ℝ→Shelf α)(u C:ℝ)(hP:ContinuousOn P Isle)(h₁:0 ≤ u)(h₂:u<1) (H:∀ t∈Isle, IsUnit (edgeM A t).det ∧ ‖paintO (τ:=α) (tea_r A P t)‖ ≤ u ∧ ‖paintO (τ:=α) (A*P t)‖ ≤ C) : HasSum (pulseX A P) (Real.log ((1+ A).det)):=by
 let p(n:ℕ)(t:ℝ):=trace (grind A P n t); have h(n:ℕ):IntegrableOn (p n) Isle := (tepid A P hP n).integrableOn_Icc
 have ht(n)(t:ℝ)(ht:t∈Isle): ‖p n t‖ ≤  (Fintype.card α:ℝ)*C*u^n:=op_trace _ _ _ _ (H t ht).2.2 (H t ht).2.1 _
 have he:Summable fun i=>∫ t in Isle,‖p i t‖:=by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h₁ h₂).mul_left ((Fintype.card α:ℝ)*C)) fun i=>?_ ; rw [Real.norm_of_nonneg (integral_nonneg fun _=> norm_nonneg _)]; exact (integral_mono_ae (h i).norm (integrable_const _) ((ae_restrict_mem measurableSet_Icc).mono fun t hh=> ht i t hh)).trans_eq (by simp [Isle,Ink.interval])
 have hK(t:ℝ)(ht:t∈Isle): (∑' i,p i t)=trace ((edgeM A t)⁻¹ * A) := (porter A (P t) t (H t ht).1 u (H t ht).2.1 h₂).tsum_eq
 have hh:= hasSum_integral_of_summable_integral_norm h he
 rw [setIntegral_congr_fun measurableSet_Icc hK] at hh
 have hs:= ResolventVolume.invoice 1 A (fun i hi=> (H i hi).1.ne_zero)
 rw [det_one, Real.log_one,sub_zero] at hs
 rw [← hs,intervalIntegral.integral_of_le zero_le_one,← integral_Icc_eq_integral_Ioc]; exact hh
end YM.CF.Neige

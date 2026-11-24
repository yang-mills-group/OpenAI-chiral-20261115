import YM.Analysis.Polydisc
import Mathlib.Analysis.Calculus.ParametricIntegral
/-!
 # Analytic integral. S measurable subset of compact K. germ uses finite decomposition.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.PortRT
open Filter Set MeasureTheory Function Topology Metric Complex Module
open scoped BigOperators Topology ContDiff NNReal ENNReal
variable {U:Type*}[NormedAddCommGroup U][NormedSpace ℂ U][FiniteDimensional ℂ U]
variable {Y:Type*}[TopologicalSpace Y][T2Space Y][MeasurableSpace Y][BorelSpace Y][SecondCountableTopology Y]{μ:Measure Y}[IsLocallyFiniteMeasure μ]
variable {A:Set U}(hA:IsOpen A){K S:Set Y}(hK:IsCompact K)(hS: MeasurableSet S)(p:S⊆K)
variable {C:Type*}[NormedAddCommGroup C](G:U→Y→C)
include hK p
lemma IntaRT {a:U}(ha:a∈A)(e:ContinuousOn (fun z:U×Y=> G z.1 z.2) (A ×ˢ K)): IntegrableOn (G a) S μ:=
 ((e.comp (continuous_const.prodMk continuous_id|>.continuousOn) (fun w hp=>⟨ha,hp⟩)|>.integrableOn_compact hK).mono_set p)
variable (F:U→Y→ℂ)(D:U→Y→U→L[ℂ] ℂ)
variable (eF: ContinuousOn (fun z:U×Y=> F z.1 z.2) (A ×ˢ K))(eD: ContinuousOn (fun z:U×Y=>D z.1 z.2) (A ×ˢ K))
variable (h:∀ x∈A,∀ y∈K,HasFDerivAt (fun x=> F x y) (D x y) x)
include eF eD h hA hS
lemma SwellDerivativeRt (x:U)(g:x∈A): HasFDerivAt (fun x=>∫ y in S,F x y ∂μ) (∫ y in S,D x y ∂μ) x:=by
 letI:=FiniteDimensional.proper ℂ U
 obtain ⟨b,hb,ht⟩:= Metric.mem_nhds_iff.mp (hA.mem_nhds g); let V:= closedBall x (b/2); have hV: V⊆A:= (closedBall_subset_ball (half_lt_self hb)).trans ht
 let M:=V ×ˢ K; obtain ⟨c,hc⟩:= ((isCompact_closedBall x (b/2)).prod hK|>.image_of_continuousOn (f:=fun z:U×Y=> ‖D z.1 z.2‖) (eD.norm.mono (prod_mono hV (Subset.refl K)))).bddAbove
 have t: μ S≠⊤:= (lt_of_le_of_lt (measure_mono p) hK.measure_lt_top).ne
 refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F:=F) (s:=V) (bound:=fun _=>c) (Metric.closedBall_mem_nhds _ (half_pos hb)) ?_ (IntaRT hK p F g eF) (IntaRT (μ:=μ) hK p D g eD|>.aestronglyMeasurable) ?_ (integrableOn_const t) ?_
 · filter_upwards [hA.mem_nhds g] with y hy; exact (IntaRT (μ:=μ) hK p F hy eF|>.aestronglyMeasurable)
 · filter_upwards [ae_restrict_mem hS] with y hy; exact fun x v=> hc ⟨(x,y),⟨v,p hy⟩, rfl⟩
 filter_upwards [ae_restrict_mem hS] with y hy; exact fun x v=> h x (hV v) y (p hy)
lemma SwellAnalyticRT: AnalyticOnNhd ℂ (fun x : U=> ∫ y in S,F x y ∂μ) A:=by
 intro x t; apply PolyDisc.finiteD; filter_upwards [hA.mem_nhds t] with w g; exact (SwellDerivativeRt (μ:=μ) hA hK hS p F D eF eD h w g).differentiableAt
#print axioms SwellAnalyticRT
end YM.PortRT
end

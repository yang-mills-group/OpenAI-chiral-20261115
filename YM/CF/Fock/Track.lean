import YM.CF.Fock.Invoice

/-! Complex unsquared increment (of factor 1/2). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Topology
open Set MeasureTheory Filter
attribute [local instance] opCStarAlgebra
section
variable {n : Type*} [DecidableEq n] [Fintype n]
lemma invoice_at {A : Op n} (h : ‖A‖ < 1) : ContinuousAt invoice A := by
  obtain ⟨r,g,u⟩ := exists_between h
  let Y := Metric.closedBall (0:Op n) r
  have ht : Y∈𝓝 A := Metric.closedBall_mem_nhds_of_mem (show A ∈ Metric.ball (0:Op n) r by simpa using g)
  let W := uIcc (0:ℝ) 1
  have hm : ContinuousOn (fun q : Op n×ℝ => ‖slope q.1 q.2‖) (Y ×ˢ W) := by
    rintro ⟨X,t⟩ ⟨hX,hY⟩
    have he : ‖X‖<1 := lt_of_le_of_lt (show _ from by simpa [Y] using hX) u
    exact (slope_j (beam_active he t hY)).norm.continuousWithinAt
  obtain ⟨c,hc⟩ := ((IsCompact.image_of_continuousOn ((isCompact_closedBall (0:Op n) r).prod isCompact_uIcc) hm)).bddAbove
  apply intervalIntegral.continuousAt_of_dominated_interval (F:=slope) (bound:=fun _=>c)
  · exact Eventually.of_forall fun A=>(slope_meas A).aestronglyMeasurable
  · filter_upwards [ht] with X hx; exact Eventually.of_forall fun x g=>hc ⟨(X,x),⟨hx,uIoc_subset_uIcc g⟩,rfl⟩
  · exact intervalIntegrable_const
  exact Eventually.of_forall fun t ht=>(slope_j (beam_active h t (uIoc_subset_uIcc ht))).comp (f:=fun X=>(X,t)) (continuousAt_id.prodMk continuousAt_const)
lemma inv_turn (U : UNI n) (A : Op n) (h : IsUnit A) : (twist U A)⁻¹=twist U A⁻¹ := by
  have he : twist U A*twist U A⁻¹=1 := by rw [←map_mul,(live h).1,map_one]
  rw [← one_mul (twist U A⁻¹), ← (live (live_of he)).2, mul_assoc, he,mul_one]
lemma bill_invariant (U : UNI n) (A : Op n) (h : ‖A‖<1) : invoice (twist U A)=invoice A := by
  apply intervalIntegral.integral_congr
  intro x hx; unfold slope
  rw [show beam (twist U A) x=twist U (beam A x) by unfold beam; rw [map_add,map_one,twist_scalar], inv_turn _ _ (beam_active h x hx),← map_mul,trace_twist]
def spark (P A C : Op n) := invoice (relay P A C-1)/2
lemma spark_equal {P A : Op n} (h : IsStarProjection P) (g : IsUnit (stage P A)) : spark P A A=0 := by simp [spark,relay_base h g,invoice,slope]
lemma spark_turn {P A C : Op n} (h : IsUnit (stage P A)) (g : ‖relay P A C-1‖ < 1) (U : UNI n) : spark (twist U P) (congrC U A) (congrC U C)=spark P A C := by
  unfold spark; rw [relay_twist h, show twist U _-1 = twist U (relay P A C-1) by rw [map_sub,map_one],bill_invariant U _ g]
lemma spark_contAt {P A C : Op n} (g : IsUnit (stage P A)) (h : ‖relay P A C-1‖ < 1) :
    ContinuousAt (fun t : Op n × Op n × Op n => spark t.1 t.2.1 t.2.2) (P,A,C) := by
  let f := fun t:Op n×Op n×Op n=>relay t.1 t.2.1 t.2.2-1
  have he : ContinuousAt f (P,A,C) := (relay_contAt g).sub continuousAt_const
  have hp : ContinuousAt (invoice ∘ f) (P,A,C) := (invoice_at (A:=f (P,A,C)) h).comp he
  exact hp.div_const 2
end
variable {n : Type*} [LinearOrder n] [Fintype n]
lemma spark_sq {A C : Op n} (U : UNI n) (s : Finset n) (h : Aᵀ= -A) (g : Cᵀ= -C) (k : IsUnit (stage (twist U (cutM s)) A))
    (e : ‖relay (twist U (cutM s)) A C-1‖<1) :
    Complex.exp (spark (twist U (cutM s)) A C) ^ 2 * stratum U s A ^ 2=stratum U s C ^ 2 := by
  rw [spark,pow_two,←Complex.exp_add,add_halves,factor _ e,strata U s h g k,add_sub_cancel]
end YM.CF.Fock

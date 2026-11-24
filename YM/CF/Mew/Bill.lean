import YM.CF.Mew.Blow
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mew
open Function Set Metric Filter MeasureTheory Finset
open scoped Topology ContDiff BigOperators Matrix Classical
variable {I E :Type*}[Fintype I][DecidableEq I][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
lemma bill_t (F:Key I→ℕ→E)(g:∀ i,River (fun v=>F v i)){f:ℕ→ℝ}(p:Summable f)(hp:∀ x∈hill I,∀ i, ‖F x i‖ ≤ f i): River (fun x=> ∑' i,F x i):=by
 let μ:Measure ℕ:= Measure.count; have hx:Integrable f μ:=MeasureTheory.integrable_count_iff.mpr p.norm
 have hv(x):AEStronglyMeasurable (F x) μ:=by exact StronglyMeasurable.of_discrete.aestronglyMeasurable -- tune
 have ht:= riverSum μ F g hx (fun x _=> hv x) hp
 exact ht.cong fun x v=> by
    symm; change (∫ i,F x i ∂Measure.count)= _; rw [Measure.count,integral_sum_measure (hx.mono' (hv _) (ae_of_all _ (hp _ v)))]; simp -- tune names
end YM.CF.Mew

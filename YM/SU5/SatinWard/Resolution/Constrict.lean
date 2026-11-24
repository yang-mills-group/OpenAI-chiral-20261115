import Mathlib
set_option maxHeartbeats 180000
noncomputable section
namespace YM.SU5.SatinWard.FieldBudgets
open Function Filter Metric
open scoped Topology NNReal Classical
variable {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V] {x:ℝ→ℝ}
variable {X K:V} {f d:ℕ → ℝ} (t:Tendsto d atTop (𝓝 0)) (P:∀ᶠ i:ℕ in atTop, ‖f i • K-X‖≤ d i)
include t P
lemma tendedR : Tendsto (fun i=>f i • K) atTop (𝓝 X):=by
 rw [tendsto_iff_norm_sub_tendsto_zero]; exact squeeze_zero' (Eventually.of_forall fun i=>norm_nonneg _) P t
variable (h:0 < ‖K‖)
include h
lemma constrict : ∃ b:ℝ, X=b • K ∧ Tendsto f atTop (𝓝 b):=by
 let M:Submodule ℝ V:= Submodule.span ℝ {K}; let s : IsClosed (M:Set V):= ((Submodule.span ℝ {K}).closed_of_finiteDimensional)
 have hv: X∈ M:= s.mem_of_tendsto (tendedR t P) (by filter_upwards with i using (M.smul_mem (f i) (Submodule.mem_span_singleton_self K))) -- include. signature .element.
 obtain ⟨b,rfl⟩:=Submodule.mem_span_singleton.mp hv
 refine ⟨b,rfl,?_⟩; rw [tendsto_iff_norm_sub_tendsto_zero]; refine squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) (?_ : ∀ᶠ i:ℕ in atTop,‖f i-b‖≤d i/‖K‖) (by simpa only [zero_div] using t.div_const ‖K‖); exact P.mono (fun i p=>(le_div_iff₀ h).mpr (by rw [←sub_smul,norm_smul] at p; exact p))
#print axioms constrict
end YM.SU5.SatinWard.FieldBudgets

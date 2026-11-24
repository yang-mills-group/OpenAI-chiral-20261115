import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Function.L2Space
import YM.CF.Bloom.Piper
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.TopPS
open Filter MeasureTheory Function Topology Metric
open scoped Topology BigOperators ENNReal InnerProductSpace
variable {E : ℕ→Type*}[∀ i,NormedAddCommGroup (E i)][∀ i,InnerProductSpace ℝ (E i)][∀ i, TopologicalSpace.SeparableSpace (E i)][∀ i,CompleteSpace (E i)]
open WeakDual
local notation "𝒴" j:max=> WeakDual ℝ (E j)
lemma treat {D:ℕ→ℝ}(A:∀ j,ℕ→ E j)(hp:∀ i j, ‖A i j‖≤ D i){R:ℕ→ Type*}[∀ i,TopologicalSpace (R i)][∀ i,CompactSpace (R i)][∀ i, FirstCountableTopology (R i)] (B:∀ i,ℕ→R i):∃ (C:∀ i,R i)(X:∀ j,E j)(z:ℕ→ℕ),StrictMono z∧ ∀ i,Tendsto (B i ∘ z) atTop (𝓝 (C i)) ∧∀ v:E i,Tendsto (fun j=> inner ℝ (A i (z j)) v) atTop (𝓝 (inner ℝ (X i) v)):=by
 let U(i): Set (𝒴 i):=WeakDual.toStrongDual ⁻¹' closedBall (0:StrongDual ℝ (E i)) (D i)
 have he(i):IsCompact (U i):= WeakDual.isCompact_closedBall _ _
 let f(i):=InnerProductSpace.toDual ℝ (E i)
 let F(i j): U i:= ⟨StrongDual.toWeakDual (f i (A i j)), mem_closedBall_zero_iff.mpr (((f i).norm_map _).trans_le (hp i j))⟩ -- name?
 letI kk:∀ i,CompactSpace (U i):=fun i=>isCompact_iff_compactSpace.mp (he i)
 letI pk:∀ i,TopologicalSpace.MetrizableSpace (U i):=fun i=> WeakDual.metrizable_of_isCompact ℝ (E i) (U i) (he i)
 let Cg(j)(i:ℕ):R i × U i:=(B i j,F i j)
 obtain ⟨S,w,f',x,v⟩:= (show IsSeqCompact (Set.univ: Set (∀ i,R i × U i)) from isCompact_univ.isSeqCompact) (fun j:ℕ=> Set.mem_univ (Cg j))
 let Q(i):= (f i).symm (toStrongDual (S i).2.val); refine ⟨fun i=>(S i).1,Q,f',x,?_⟩
 intro i; have he:= ((continuous_apply i).tendsto _).comp v; refine ⟨(continuous_fst.tendsto _).comp he,?_⟩
 intro u; have hx:= ((WeakDual.eval_continuous u).tendsto ((S i).2.val)).comp ((continuous_subtype_val.tendsto _).comp ((continuous_snd.tendsto _).comp he)); change Tendsto _ _ (𝓝 (inner ℝ (InnerProductSpace.toDual ℝ (E i) |>.symm (toStrongDual (S i).2.val)) u)); rw [InnerProductSpace.toDual_symm_apply]; exact hx
end YM.CF.TopPS

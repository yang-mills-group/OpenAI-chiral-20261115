import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
/-!
# SeparableOrbit: avoid assuming Borel ≈ continuous in sup norm
-/
noncomputable section
set_option autoImplicit false
namespace YM.SelectionAnalysis
open Function Set Filter Topology Metric MeasurableSpace MeasureTheory TopologicalSpace ENNReal

lemma measurable_evaluated {X Y Z I : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace X] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace Z] (f : Z → X) (h : IsSeparable (range f))
    (evaluation : I → X → Y) (v : ∀ i, Continuous (evaluation i))
    (p : ∀ x y, (∀ i,evaluation i x=evaluation i y) → x=y)
    (q : ∀ i, Measurable (evaluation i ∘ f)) : StronglyMeasurable f := by
  letI := borel X; haveI : BorelSpace X := ⟨rfl⟩
  let S := closure (range f)
  haveI : SeparableSpace S := TopologicalSpace.IsSeparable.separableSpace h.closure -- tune
  haveI : CompleteSpace S := isClosed_closure.completeSpace_coe
  let U (i : I) : Set ((↑S : Type _)×S) := {v | evaluation i v.1.val≠evaluation i v.2.val}
  have ho(i:I): IsOpen (U i) := (isClosed_eq ((v i).comp (continuous_subtype_val.comp continuous_fst)) ((v i).comp (continuous_subtype_val.comp continuous_snd))).isOpen_compl
  obtain ⟨s,hc,hS⟩ := (HereditarilyLindelofSpace.isLindelof (⋃ i, U i)).elim_countable_subcover U ho (Subset.refl _)
  haveI := hc.to_subtype
  let e (x : S) (i : (↑s:Type _)) := evaluation i x.val
  have ht : Injective e := by
    intro a b k; by_contra h
    have he : ∃ i, evaluation i a.val≠ evaluation i b.val := not_forall.mp fun h' => h (Subtype.ext (p a b h'))
    obtain ⟨u,v⟩ := he; obtain ⟨i,h⟩ := Set.mem_iUnion.mp (hS (mem_iUnion.mpr ⟨u,(show (a,b)∈U u from v)⟩)); obtain ⟨q,k'⟩ := mem_iUnion.mp h
    exact (show evaluation i a.val ≠ evaluation i b.val from k') (congrFun k ⟨i,q⟩)
  have he : Continuous e := continuous_pi (fun i => (v i).comp continuous_subtype_val)
  let f' (i:Z) : S := ⟨f i,subset_closure (mem_range_self _)⟩
  have hf : Measurable f' := (he.measurableEmbedding ht).measurable_comp_iff.mp (measurable_pi_lambda _ fun i => q i)
  exact stronglyMeasurable_iff_measurable_separable.mpr ⟨measurable_subtype_coe.comp hf,h⟩
end YM.SelectionAnalysis
#print axioms YM.SelectionAnalysis.measurable_evaluated

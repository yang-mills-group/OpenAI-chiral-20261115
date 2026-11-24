import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.Maps.Proper.Basic

/-! Compact-valued Borel choice and standard Borel extension lemmas, for the Mark
prescriptions. All assertions pointwise. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof
open Function TopologicalSpace Topology MeasureTheory Metric Filter Set
open scoped Topology NNReal ENNReal
section Selection
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MetricSpace Y] [BorelSpace Y]
    [CompactSpace Y] [Nonempty Y]

private structure Fiber where
  carrier : X → Set Y
  closed (x) : IsClosed (carrier x)
  ne (x) : (carrier x).Nonempty
  hit (T : Set Y) (h : IsClosed T) : MeasurableSet {x | (carrier x ∩ T).Nonempty}

private lemma Fiber.next (F : Fiber (X:=X) (Y:=Y)) (ε : ℝ) (hε : 0<ε) :
    ∃ (H : Fiber (X:=X) (Y:=Y)) (f : X → Y), Measurable f ∧ ∀ x,
        H.carrier x ⊆ F.carrier x ∩ closedBall (f x) ε := by
 classical
 let b:= denseSeq Y; let R (n) := closedBall (b n) ε
 have hh (x : X) : ∃ i, (F.carrier x ∩ R i).Nonempty:=by
   obtain ⟨y,hy⟩:=F.ne x; obtain ⟨n, hn⟩:= DenseRange.exists_dist_lt (denseRange_denseSeq Y) y hε
   exact ⟨n, y, hy, mem_closedBall.mpr hn.le⟩
 let I(x):= Nat.find (hh x)
 have hm:Measurable I:= measurable_find hh fun k => F.hit _ isClosed_closedBall
 let S(x):= F.carrier x∩ R (I x)
 refine ⟨⟨S, fun x=> (F.closed x).inter isClosed_closedBall,fun x=> Nat.find_spec (hh x),?_⟩, b ∘ I,(measurable_of_countable _).comp hm, fun _=>Subset.rfl⟩
 intro T hT
 rw [show {x|(S x∩T).Nonempty}=⋃ i : ℕ, (I ⁻¹' {i}) ∩ {x|(F.carrier x∩(R i∩T)).Nonempty} from ?_]
 · exact MeasurableSet.iUnion fun i=>(hm (measurableSet_singleton _)).inter (F.hit _ (isClosed_closedBall.inter hT))
 ext x; simp [S,inter_assoc]

theorem compact_choice (F : X→Set Y) (hc : ∀ x, IsClosed (F x)) (hne : ∀ x, (F x).Nonempty)
    (hp : ∀ T : Set Y,IsClosed T → MeasurableSet {x|(F x ∩ T).Nonempty}) : ∃ f : X→Y,Measurable f ∧ ∀ x,f x∈ F x := by
 classical
 let u : Fiber (X:=X) (Y:=Y):=⟨F,hc,hne,hp⟩
 obtain ⟨ε,-,hε,ht⟩ := exists_seq_strictAnti_tendsto (0:ℝ)
 choose g q H h using fun n (F : Fiber (X:=X) (Y:=Y)) => F.next (ε n) (hε n)
 let D (n : ℕ) : Fiber (X:=X) (Y:=Y) := Nat.rec (motive:=fun _=>_)  u (fun i b => g i b) n
 have hk x (i : ℕ) : (D (i+1)).carrier x ⊆ (D i).carrier x∩closedBall (q i (D i) x) (ε i):= h ..
 choose f hf using fun x=> IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _
   (fun i => (hk x i).trans inter_subset_left) (fun i => (D i).ne x) ((D 0).closed x).isCompact (fun i=> (D i).closed x)
 refine ⟨f,measurable_of_tendsto_metrizable (f:=fun i=>q i (D i)) (fun i => H ..) (tendsto_pi_nhds.mpr fun x => ?_),fun x=>mem_iInter.mp (hf x) 0⟩
 apply Metric.tendsto_nhds.mpr
 intro e he
 filter_upwards [ht.eventually (gt_mem_nhds he)] with i hi
 rw [dist_comm]; exact ((hk x i (mem_iInter.mp (hf x) (i+1))).2 : dist (f x) _ ≤ ε i).trans_lt hi
end Selection

theorem closed_choice {X Y : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X] [MeasurableSpace Y] [TopologicalSpace Y] [CompactSpace Y] [MetrizableSpace Y] [BorelSpace Y] [Nonempty Y]
    (F : Set (X×Y)) (hc : IsClosed F) (h : ∀ x : X, ∃ y : Y,(x,y)∈F) :
    ∃ f : X→Y, Measurable f ∧ ∀ x,(x,f x)∈F := by
 letI := TopologicalSpace.metrizableSpaceMetric Y
 apply compact_choice (fun x=> {y | (x,y)∈F}) (fun x=> hc.preimage (by fun_prop : Continuous fun y : Y => (x,y))) h
 intro T ht
 rw [show {x : X|({y | (x,y)∈F} ∩ T).Nonempty}=Prod.fst '' (F ∩ Prod.snd ⁻¹' T) from ?_]
 · exact (isClosedMap_fst_of_compactSpace _ (hc.inter (ht.preimage continuous_snd))).measurableSet
 ext x; simp [Set.ext_iff,Set.Nonempty]
end YM.CF.BProof

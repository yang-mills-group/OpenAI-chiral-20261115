import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Maps.Proper.Basic
/-!
Measurable choice on a compact fiber. Closed, **not** e.g. arbitrary Borel, relation.
Used for the Borel options in the frame prescriptions of B-gate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress
open Function Filter Metric TopologicalSpace MeasureTheory Set
open scoped Topology Classical
variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace Y] [MetrizableSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] [Nonempty Y]

lemma closed_selector (s : Set (X × Y)) (h : IsClosed s) (p : ∀ x, ∃ y, (x,y)∈s) :
    ∃ f : X → Y, Measurable f ∧ ∀ x, (x,f x) ∈ s := by
  letI := metrizableSpaceMetric Y
  let q:= denseSeq Y; let u (n:ℕ):ℝ:= (1/2)^n
  have he(n:ℕ):0<u n:= by unfold u; positivity
  have hs (y : Y)(n): ∃ i, dist y (q i) ≤ u n:= ((Metric.denseRange_iff.mp (denseRange_denseSeq Y)) y (u n) (he _)).imp fun _ h=> h.le
  let P (n i:ℕ) := Prod.fst '' (s ∩ Prod.snd ⁻¹' closedBall (q i) (u n))
  have hp (n i): MeasurableSet (P n i) := (isClosedMap_fst_of_compactSpace _ (h.inter (isClosed_closedBall.preimage continuous_snd))).measurableSet
  have eh n i x : x ∈ P n i ↔ ∃ y, (x,y)∈s∧ dist y (q i) ≤ u n := by
    constructor
    · rintro ⟨⟨x,y⟩,⟨v,p⟩,rfl⟩; exact ⟨y,v, p⟩
    rintro ⟨y,v,p⟩; exact ⟨(x,y),⟨v,p⟩,rfl⟩
  let Z(n:ℕ):= { g : X → ℕ // Measurable g ∧ ∀ x, x ∈ P n (g x) }
  have h0 : Nonempty (Z 0) := by
    have H (x:X) : ∃ i, x∈ P 0 i := by
      obtain ⟨y,P'⟩:=p x; exact (hs y 0).imp fun i h=>(eh 0 i x).mpr ⟨y,P',h⟩
    exact ⟨⟨_,measurable_find H (hp 0),fun x=>Nat.find_spec (H x)⟩⟩
  have step (n) (v : Z n) : ∃ g : Z (n+1), ∀ x, dist (q (v.val x)) (q (g.val x)) ≤ 2 * u n := by
    let V (x:X) (i:ℕ) := x∈P (n+1) i ∧ dist (q (v.val x)) (q i) ≤ 2 * u n
    have H (x:X) : ∃ i, V x i := by
      obtain ⟨y,A,p⟩:=(eh n _ x).mp (v.property.2 x); obtain ⟨i,t⟩:=hs y (n+1); refine ⟨i,(eh (n+1) _ x).mpr ⟨y,A,t⟩,?_⟩; apply (dist_triangle_left ..).trans ((add_le_add p t).trans ?_); have h:=he n; unfold u at *; rw [pow_succ]; linarith
    have hV (i:ℕ):MeasurableSet {x| V x i}:=(hp _ i).inter (measurableSet_le ((show Measurable q from measurable_of_countable q).comp v.property.1|>.dist measurable_const) measurable_const)
    exact ⟨⟨fun x=>Nat.find (H x),measurable_find H hV,fun x=>(Nat.find_spec (H x)).1⟩,fun x=>(Nat.find_spec (H x)).2⟩
  choose stride H using step
  let f (n:ℕ) : Z n:= Nat.rec (motive:= Z) h0.some stride n
  let g (n:ℕ) := q ∘ (f n).val
  choose W R using fun x : X=> cauchySeq_tendsto_of_complete (u:=fun n=>g n x) (cauchySeq_of_le_geometric (1/2) 2 (by norm_num) (fun n=>H n (f n) x))
  refine ⟨W, measurable_of_tendsto_metrizable (fun n : ℕ=> (measurable_of_countable q).comp (f n).property.1) (tendsto_pi_nhds.mpr R),fun x=>?_⟩
  choose y E A using fun n=> (eh n _ x).mp ((f n).property.2 x)
  have he : Tendsto y atTop (𝓝 (W x)):= (R x).congr_dist (squeeze_zero (fun _=> dist_nonneg) (fun n=> (dist_comm ..).trans_le (A n)) (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)))
  exact h.mem_of_tendsto (tendsto_const_nhds.prodMk_nhds he) (Eventually.of_forall E)
lemma choose_if_closed (s : Set (X × Y)) (h : IsClosed s) :
    ∃ f : X → Y, Measurable f ∧ ∀ x, (∃ y, (x,y)∈s) → (x,f x) ∈ s := by
  let S:=Prod.fst '' s; let T:= ((fun p : S × Y => (p.1.val, p.2)) ⁻¹' s)
  obtain ⟨f,hf,t⟩:= closed_selector T (h.preimage ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)) (by rintro ⟨x, ⟨⟨x,y⟩,p,rfl⟩⟩; exact ⟨y,p⟩)
  refine ⟨fun x=> if h : x ∈ S then f ⟨x,h⟩ else Classical.arbitrary _,?_,fun x h=>?_⟩
  · exact Measurable.dite hf (show Measurable (fun _ : ↑Sᶜ=> Classical.arbitrary Y) from measurable_const) (isClosedMap_fst_of_compactSpace s h).measurableSet
  obtain ⟨y,v⟩:=h; have e:x ∈ S:=⟨(x,y),v,rfl⟩; simp only [dif_pos e]; exact t ⟨x,e⟩
end YM.CF.BPress

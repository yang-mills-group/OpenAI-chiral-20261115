import YM.CF.Buffered.Hilbert
import YM.CF.Buffered.Trace

/-!
# Conventional trace interpretation of the layer identities

Counting tape times pack. Include Hilbert-space trace and Hilbert-space
adjoint theorems even though the proof works entirely by kernel contraction.
No basis is fixed.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Buffered.Heat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology ComplexOrder
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
open RP Spark RG WilsonStartup Vale Scroll Spire Nova Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {m B : Side} {c : Phase.Part m B} {e d a₁ a₂ : ℝ}

local notation "μ" => wheel m B
local notation "cnt" => Measure.count
local notation "K" => Pack m B
local notation "X" n => Tape m B n × Pack m B
abbrev Kernel (m B : Side) (n:ℕ) := Tape m B n → Tape m B n → Pack m B × Pack m B → ℂ
instance (n : ℕ) : MeasurableSpace (Tape m B n) := ⊤
instance (n : ℕ) : DiscreteMeasurableSpace (Tape m B n) := inferInstanceAs (@DiscreteMeasurableSpace _ ⊤)
lemma count_generated (n : ℕ) : MeasurableSpace.CountablyGenerated (X n) := inferInstance
attribute [local instance] count_generated
instance count_hilb (n : ℕ) : SecondCountableTopology (HS.Hilb (Measure.count.prod μ : Measure (X n))) := by
  haveI : Fact ((2: ENNReal) ≠ ⊤) := ⟨by simp⟩
  apply Lp.SecondCountableTopology

def merge {n : ℕ} (V : Kernel m B n) (x : (X n) × (X n)) := V x.1.1 x.2.1 (x.1.2,x.2.2)
lemma merge_env {n : ℕ} (V : Kernel m B n) (h : ∀ j k, Envelope (V j k)) : Envelope (merge V) := by
  let W (p : (Tape m B n×Tape m B n)×(K×K)):= V p.1.1 p.1.2 p.2
  choose C hC using fun j k=> (h j k).cost
  refine ⟨(show Measurable W from measurable_from_prod_countable_right fun i=> (h i.1 i.2).meas).comp (((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)).prodMk ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))), ∑ i, ∑ j, max 0 (C i j), fun x=> ?_⟩
  exact (hC _ _ _).trans <| (le_max_right ..).trans <| (single_le_sum (f:=fun j=> max 0 (C x.1.1 j)) (fun i _=> le_max_left ..) (mem_univ x.2.1)).trans (single_le_sum (fun i _=> sum_nonneg (fun _ _=> le_max_left ..)) (mem_univ x.1.1))

lemma merge_dual {n : ℕ} (V : Kernel m B n) : merge (kernelStar n V)=HS.dual (merge V) := rfl
lemma merge_trace {n : ℕ} {V W : Kernel m B n} (h : ∀ j k, Envelope (V j k)) (g : ∀ j k, Envelope (W j k)) :
      HS.trace (Measure.count.prod μ) (merge V) (merge W)=kernelTrace n V W := by
  let S:= Tape m B n
  let t (x : (X n) × (X n)) := merge V x * merge W x.swap
  have ht:=env_mult (merge_env V h) (Env.along (merge_env W g) measurable_swap)
  unfold kernelTrace HS.trace; change (∫ x, t x ∂ (Measure.count.prod μ).prod (Measure.count.prod μ)) =_
  -- swap inner meas or use fourway measure-preserving via equiv
  rw [integral_prod _ (Env.integrableX (f:=t) ht _)] -- split two outer
  rw [integral_prod]; swap; · exact (Env.integrableX (f:=t) ht _).integral_prod_left -- check side
  rw [integral_count]; refine sum_congr rfl fun i _=> ?_
  have hw (x : X n) : Envelope (fun y => t (x,y)) := Env.along ht (measurable_const.prodMk measurable_id)
  have hv (x : X n) := integral_prod (fun y=>t (x,y)) (Env.integrableX (hw x) (Measure.count.prod μ))
  simp_rw [hv, integral_count]
  rw [integral_finsetSum]; swap
  · intro s _; exact (Env.integrableX (env_marginal (f:= fun p : K×K=>t ((i,p.1),(s,p.2))) (Env.along ht ((measurable_const.prodMk measurable_fst).prodMk (measurable_const.prodMk measurable_snd))) _) _)
  refine sum_congr rfl fun j _=> ?_
  exact (integral_prod _ (trace_integrable _ _ h g i j)).symm

variable {n:ℕ} {V W : Kernel m B n}
open HS

abbrev HSpace (m B : Side) (n : ℕ) := Hilb (Measure.count.prod (wheel m B) : Measure (Tape m B n×Pack m B))
def operator (h : ∀ j k, Envelope (V j k)) : HSpace m B n →L[ℂ] HSpace m B n := ofKernel (Measure.count.prod μ) (merge_env _ h)
lemma trace_operator (h : ∀ j k, Envelope (V j k)) (p : ∀ j k, Envelope (W j k)) {ι : Type*} (b : HilbertBasis ι ℂ (HSpace m B n)) :
      HasSum (fun i=> ⟪b i,operator h (operator p (b i))⟫_ℂ) (kernelTrace n V W) := by
  rw [←merge_trace h p]; exact traceBasis _ _ _ b
lemma adjoint_operator (h : ∀ j k, Envelope (V j k)) : operator (star_env h)=(operator h).adjoint := hilbertAdjoint (Measure.count.prod μ) (merge_env V h)
lemma trace_at_layer (p : Pinning m B) (W : Scroll m B c) (clip : Clip) (β t u : ℝ) (b : Budget B e d) (H : ScaleK a₁ a₂ W) (i : Axis) (cut : Foot m B) (hu : 0 ≤ u) (n : ℕ) (f g : RP.Test m B) (hf : NorthMark i f) (hg : NorthMark i g)
      {ι : Type*} (B' : HilbertBasis ι ℂ (HSpace m B (n+1))) :
    let F := operator (transfer_env p W clip β t u b H i cut (n:=n) f hf.envelope)
    let G := operator (transfer_env p W clip β t u b H i cut (n:=n) g hg.envelope)
    HasSum (fun j=> ⟪ B' j, G (ContinuousLinearMap.adjoint F (B' j))⟫_ℂ)
     (∫ x, slabTerm p W clip β t e (testProduct i f g) (hotEvol i cut u n) x ∂wheel m B) := by
  dsimp only; rw [←adjoint_operator, at_layer p W clip β t u b H _ _ hu _ _ _ hf hg]; exact trace_operator _ _ _
end YM.CF.Buffered.Heat
#print axioms YM.CF.Buffered.Heat.trace_at_layer

import YM.CF.Phase.Log
import Mathlib.MeasureTheory.Integral.Pi

/-! Sphere probability, product laws, continuous integrals. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Phase
open Cube Lat Lattice SU Fock Filter MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace Topology
attribute [local instance] opCStarAlgebra

def first : Ballot := ⟨basisKet 0,by simp [Sphere,basisKet]⟩
def turns (g : E) := scaledV g first
lemma turns_cont : Continuous turns := by
  let f := fun g:E => (g,first)
  change Continuous ((fun q:E×Ballot=>scaledV q.1 q.2) ∘ f); exact scaled_cont.comp (show Continuous f from continuous_id.prodMk continuous_const)
lemma sphere_onto : Function.Surjective turns := by
  rintro ⟨x,h⟩
  obtain ⟨u,H⟩ := SU.Pair.reachable x (vote_unit ⟨x,h⟩)
  refine ⟨u,Subtype.ext ?_⟩; apply PiLp.ext; intro i; exact congr_fun H _

def cloud : Measure Ballot := SU.group.probHaar.map turns
instance : IsProbabilityMeasure cloud := Measure.isProbabilityMeasure_map turns_cont.aemeasurable -- tune
instance : cloud.IsOpenPosMeasure := turns_cont.isOpenPosMeasure_map sphere_onto
lemma drop_cont (g : E) : Continuous (scaledV g) := by
  let f := fun x:Ballot => (g,x)
  change Continuous ((fun q:E×Ballot=>scaledV q.1 q.2) ∘ f); exact scaled_cont.comp (show Continuous f from continuous_const.prodMk continuous_id)
lemma drop_inv (g : E) (x : Ballot) : scaledV g⁻¹ (scaledV g x)=x := Subtype.ext (turn_inv_g ..)
def dropE (g : E) : Ballot ≃ᵐ Ballot where
  toFun := scaledV g
  invFun := scaledV g⁻¹
  left_inv := drop_inv g
  right_inv x := by nth_rw 1 [←inv_inv g]; exact drop_inv g⁻¹ _
  measurable_toFun := (drop_cont _).measurable
  measurable_invFun := (drop_cont _).measurable
lemma drop_map (g : E) : MeasurePreserving (scaledV g) cloud cloud := by
  constructor
  · exact (drop_cont _).measurable
  unfold cloud; rw [Measure.map_map (drop_cont _).measurable turns_cont.measurable,
    show (scaledV g ∘ turns)=turns ∘ (fun x=>g*x) by funext x; exact Subtype.ext (turn_seq g x _).symm,
    ←Measure.map_map turns_cont.measurable (measurable_const_mul g), (measurePreserving_mul_left SU.group.probHaar g).map_eq]

def rains (m : Side) : Measure (Cue m) := Measure.pi fun _=> cloud
instance (m : Side) : IsProbabilityMeasure (rains m) := by unfold rains; infer_instance
def pass (m B : Side) (g : Site (Domain m B)→E) : Cue m ≃ₜ Cue m where
  toFun := partner m B g
  invFun := partner m B (fun x=> (g x)⁻¹)
  left_inv x := funext fun i=>drop_inv _ _
  right_inv x := funext fun i=> (dropE _).right_inv _ -- tune
  continuous_toFun := continuous_pi fun i=>(drop_cont _).comp (continuous_apply i)
  continuous_invFun := continuous_pi fun i=>(drop_cont _).comp (continuous_apply i)
lemma rain_g (m B : Side) (g : Site (Domain m B)→E) : MeasurePreserving (partner m B g) (rains m) (rains m) := measurePreserving_pi _ _ fun i=>drop_map (g (address m B i))
lemma net_compact {K A : Type*} [NormedAddCommGroup K] [MeasurableSpace A] [TopologicalSpace A] [CompactSpace A] [T2Space A] [BorelSpace A] {f : A→K} {μ : Measure A} [IsFiniteMeasure μ] (h : Continuous f) : Integrable f μ := h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
lemma rain_subst {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K] (m B : Side) (g : Site (Domain m B)→E) (f : Cue m→K) :
    ∫ a, f (partner m B g a) ∂rains m = ∫ a, f a ∂rains m := (rain_g m B g).integral_comp (pass m B g).measurableEmbedding _
section
variable {K A X : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K] [MeasurableSpace A] [TopologicalSpace A] [CompactSpace A]
    [T2Space A] [BorelSpace A] [TopologicalSpace X]
lemma net_cont [FirstCountableTopology X] [LocallyCompactSpace X] (f : X × A→K) (μ : Measure A) [IsFiniteMeasure μ] (h : Continuous f) : Continuous (fun x : X=> ∫ a:A, f (x,a) ∂μ) := by
  rw [continuous_iff_continuousAt]; intro x
  obtain ⟨L,hL,g⟩ := exists_compact_mem_nhds x -- order?
  obtain ⟨c,hc⟩ := (hL.prod (@isCompact_univ A _ _)).image h.norm |>.bddAbove
  apply continuousAt_of_dominated (bound:=fun _=>c)
  · exact Eventually.of_forall fun a=>(net_compact (f:=fun x=> f (a,x)) (μ:=μ) (h.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  · filter_upwards [g] with x hx; exact Eventually.of_forall fun y=>hc ⟨(x,y),⟨hx,Set.mem_univ y⟩,rfl⟩
  · exact integrable_const _
  exact Eventually.of_forall fun y => (show Continuous (fun i=>f (i,y)) from h.comp (continuous_id.prodMk continuous_const)).continuousAt
end
end YM.CF.Phase

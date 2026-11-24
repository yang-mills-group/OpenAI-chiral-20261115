/- This file incorporates modified third-party source. See the source attributions in notices/. -/ -- Adapted/namespace-shifted from repository YM.Fields.Spectrum for Styria trajectory-L use. S and T differ; hypotheses apply only explicitly, no LRoom assumed to be full OS.
import GaugeFieldConstruction.StyriaRel.YM.Fields.System
import GaugeFieldConstruction.StyriaRel.YM.Heat.Lift

import GaugeFieldConstruction.StyriaRel.YM.Shift.Swap



/-!
# Uniqueness and forwardum for ANY subword covariant domain

From a specified isometric intertwiner for translations into SAME or selected
chamber. No gap. Use M.test rolls on negative directions; no cones assumed
on OS. Projection identity proved at Hilbert level.
-/
set_option autoImplicit false
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary
open Function Set Filter MeasureTheory Measure OS Mink Probe Spectral Complex
open scoped Topology NNReal BigOperators InnerProductSpace ComplexOrder
variable {G : Gauge} {L : Register G} {S : Table L} {X : Hilbert}

namespace Action
variable (P : Action X)
def spaceKeep (s : Poincare) : X→ₗᵢ[ℂ] X := ⟨(P.V s).toLinearMap,P.usual s⟩
lemma flavor (s : Poincare) (x y : X) : inner ℂ (P.V s x) (P.V s y)=inner ℂ x y := (P.spaceKeep s).inner_map_map _ _

def μ (x : X) := P.orbit.P.diagonal x
instance (x : X) : IsFiniteMeasure (P.μ x) := P.orbit.P.finite _
lemma placed (r : Lorentz) (x : X) : P.μ (P.V (Poincare.motion r) x) = (P.μ x).map (Lorentz.act (Lorentz.dual r)) := by
  have he (p : E4) : Poincare.translation (r.act p)*Poincare.motion r=Poincare.motion r*Poincare.translation p := by
    apply Poincare.by_placement;intro b;simp
  have hm : IsFiniteMeasure ((P.μ x).map (Lorentz.act (Lorentz.dual r))) := by infer_instance
  apply Measure.ext_of_charFun; ext1 b
  obtain ⟨p,rfl⟩ := r.sends.surjective b
  have hx : charFun (P.μ (P.V (Poincare.motion r) x)) (r.act p) = charFun (P.μ x) p := by
    unfold μ; rw [P.orbit.total,P.orbit.total]
    change inner ℂ _ (P.V (Poincare.translation (r.act p)) (P.V _ _)) = inner ℂ _ (P.V (Poincare.translation p) x)
    rw [← ContinuousLinearMap.comp_apply, ← P.mult,he p,P.mult]; exact P.flavor ..
  rw [Lorentz.sent,hx, charFun_apply,charFun_apply, integral_map _ _]; rotate_left
  · exact (ContinuousLinearMap.continuous _).measurable.aemeasurable
  · exact (show Continuous (fun y : E4 => Complex.exp ((↑(inner ℝ y (r.act p)):ℂ)*I)) from by fun_prop).aestronglyMeasurable
  congr! 3
  simpa using (Lorentz.dual_sent (Lorentz.dual r) p _).symm

/-- every direction sharpened; true spectrum not just symbols. -/
lemma south (hp : ∀ v : X, (P.μ v).support ⊆ {p : E4|0 ≤ p timeAxis}) : P.orbit.P.region coneᶜ=0 := by
  have h v : (P.μ v).support ⊆ cone := fun x hx => (Lorentz.from_half x).2 fun r => by
    apply hp (P.V (Poincare.motion r) v); rw [P.placed]
    apply Measure.mem_support_iff_forall _|>.mpr
    intro A hA
    obtain ⟨U,hU,hu,hA'⟩ := mem_nhds_iff.mp hA
    refine lt_of_lt_of_le ?_ (measure_mono hU)
    rw [Measure.map_apply (ContinuousLinearMap.continuous _).measurable hu.measurableSet]
    exact ((Measure.mem_support_iff_forall _).1 hx _ ((hu.preimage (ContinuousLinearMap.continuous _)).mem_nhds hA'))
  ext1 x
  apply (P.orbit.P.null_pair closed_cone.isOpen_compl.measurableSet _).mp
  exact measure_mono_null (compl_subset_compl.mpr (h x)) (measure_compl_support)
end Action

-- A room ON THIS theory, without assumption of UniqueHeat on all (ground-axis question), or that operator costs at ties. Slice calibration invokes actual fields.
structure LRoom {G : Gauge} {L : Register G} (_S : Table L) (a : Axis) where
  H : Hilbert
  flow : OS.Semigroup H a
  omega : H
  norm : ‖omega‖=1
  vacs (x): flow.U x omega=omega
  vacT (x): flow.E x omega=omega
def LRoom.jointLine (C:LRoom S timeAxis) := ∀ v:C.H, (∀ x, C.flow.unit.translation x v=v)→ ∃ z:ℂ,z • C.omega=v

namespace Action
variable {C : LRoom S timeAxis} (P : Action X) {W : X→L[ℂ] C.H}

/-- W maps into the chamber but distinguished Vacuum AND flows proved
later/specified before projection; not arbitrary filter limits. -/
structure Intervenes (W : X→L[ℂ] C.H) (v : X) : Prop where
  scale (x : X) : ‖W x‖=‖x‖
  across (p) : W.comp (P.orbit.translation p) = (C.flow.unit.translation p).comp W
  start : W v=C.omega

lemma spectrum {w : X} (h : P.Intervenes (C := C) W w) : P.orbit.P.region coneᶜ=0 := by
  refine P.south fun x => ?_
  have he : P.μ x=C.flow.ℚmeasure.diagonal (W x) := by
    apply Measure.ext_of_charFun; ext1 i; unfold μ; rw [P.orbit.total,C.flow.joint]
    rw [← ContinuousLinearMap.comp_apply _ W,h.across i |>.symm]
    exact (LinearIsometry.inner_map_map (⟨W.toLinearMap,h.scale⟩ : X →ₗᵢ[ℂ] C.H) x _).symm
  rw [he]; exact C.flow.nonneg _

theorem only {w : X} (h : P.Intervenes (C:=C) W w) (hc : C.jointLine) (x : X) (hp : ∀ i,P.orbit.translation i x=x) :
    ∃ z : ℂ,z • w=x := by
  obtain ⟨z,H⟩ := hc (W x) fun b => by
    rw [← ContinuousLinearMap.comp_apply _ W, ← h.across, ContinuousLinearMap.comp_apply,hp]
  refine ⟨z,(show Injective W from (⟨W.toLinearMap,h.scale⟩ : X→ₗᵢ[ℂ] C.H).injective) ?_⟩
  rw [map_smul,h.start];exact H
end Action
end YM.NSF.Boundary

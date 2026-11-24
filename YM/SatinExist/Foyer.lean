import SatinGlasshouseReadingNovember6
import YM.SU5.Selected.Reserved
import YM.SU5.Selected.Landing
/-!
# Match orientations and actual full resolution Hilbert channels

On P, take character on the axis 3 display, then apply CP27 displacement off that very
character for its orientation j probability, EXACTLY as in the inputs BoostBacking etc.
No χ assumptions. The drive algebras and even the chosen clocks could in principle differ.
Use BP's axioms through CP18 consistency and show the direct *Gram identification on all words*
as in reconstruction manuscript XVII's spirit. Then transport the positive- and real-time
semigroups and spatial grid motions.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4000
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup
open MacroGrid Set
variable (P : Spine) (x : P.Spectrum0 3) (j : Axis)
local notation "Y" => P.run
local notation "H" => P.large
local notation "Λ" => P.par
local notation "V" => P.law
local notation "G" => P.history
local notation "Gt" => P.projection.clipped
local notation "W" => timeMesh P.par
local notation "C" => P.room
local notation "ξ" => P.advocate 3 x j
local notation "ζ" => P.glasshouseCharacter 3 x

abbrev orientHouse := Selected.displacement Y H V G Gt 3 false (C 3) ζ j (C j)
local notation "χ" => P.orientHouse x j
abbrev GreatRoom := Selected.indoor Y H V G Gt j false (C j) χ
local notation "Hi" => P.GreatRoom x j
local notation "Hz" => P.PortionHil j ξ
local notation "Hc" => P.ColorHil j ξ
abbrev greatBud (s:ℕ)(b:P.Vox j s) : P.GreatRoom x j := Selected.bud Y H V s G Gt j false (C j) χ b
local notation "Bc" => P.stateVox j ξ
local notation "Bg" => P.greatBud x j

lemma orientHouse_report (s:ℕ)(b:P.Test) :
    P.singleState j s ξ b = Selected.response Y H V s G Gt j false (C j) χ
      (P.glasshouseMark b) := by
  rw [Selected.across_response, P.glasshouseResponse_eq]
  exact P.single_agrees ..

lemma greatGram (s t:ℕ)(b:P.Vox j s)(d:P.Vox j t) :
    inner ℂ (Bc s b) (Bc t d) = inner ℂ (Bg s b) (Bg t d) := by
  let k:=max s t; let e:=le_max_left s t; let g:=le_max_right s t
  unfold greatBud
  rw [←P.refine_vox j ξ s _ e, ←P.refine_vox j ξ t _ g, ←Selected.flourishes Y H V s G Gt j false (C j) χ _ e,
    ←Selected.flourishes Y H V t G Gt j false (C j) χ _ g]
  rw [P.gram_at, Selected.earns, P.orientHouse_report]; rfl

local notation "I" => Σ s:ℕ,P.Vox j s
abbrev preGramSeeds (i:Σ s:ℕ,P.Vox j s) : P.PortionHil j (P.advocate 3 x j) := Bc i.1 i.2
abbrev gramSeeds (i:Σ s:ℕ,P.Vox j s) : P.GreatRoom x j := Bg i.1 i.2
lemma preGram_dense : Dense (Submodule.span ℂ (Set.range (P.preGramSeeds x j)) : Set Hz) := by
  refine (P.all_cyclic j ξ).mono (Submodule.span_mono ?_)
  rintro i p; obtain ⟨s,b,h⟩:= Set.mem_iUnion.mp p
  exact ⟨⟨s,b⟩,h⟩
lemma gram_dense : Dense (Set.range (P.gramSeeds x j)) := by
  refine (Selected.stroll_dense Y H V G Gt j false (C j) χ).mono ?_
  rintro i p; obtain ⟨s,b,h⟩:= Set.mem_iUnion.mp p
  exact ⟨⟨s,b⟩,h⟩
lemma greatBridge : ∃ e : (P.PortionHil j ξ).space ≃ₗᵢ[ℂ] (Hi).space,
    ∀ (s:ℕ)(b:P.Vox j s),e (P.stateVox j ξ s b) = P.greatBud x j s b := by
  obtain ⟨e,p⟩ := intertwine («A»:=Hz) («B»:=Hi) (P.preGramSeeds x j) (P.gramSeeds x j)
    (P.preGram_dense x j) ((P.gram_dense x j).mono (Submodule.subset_span)) (fun i k => P.greatGram x j i.1 k.1 i.2 k.2)
  exact ⟨e,fun s b => p ⟨s,b⟩⟩
noncomputable def foyer : (P.PortionHil j (P.advocate 3 x j)) ≃ₗᵢ[ℂ] P.GreatRoom x j :=
  (P.greatBridge x j).choose
local notation "α" => P.foyer x j
lemma foyer_bud (s:ℕ)(b:P.Vox j s) : α (Bc s b) = Bg s b := (P.greatBridge x j).choose_spec ..
lemma foyer_vacuum : α (P.emptyV j ξ) = Selected.doorstep Y H V G Gt j false (C j) χ := by
  rw [←P.voxel_stays, P.foyer_bud]; exact Selected.root ..

/-- CP27's actual gauge averaging ensures that CP18's smaller native color sector
also covers the full loose Hilbert. No spatial continuity price is paid yet.
-/
lemma neutral_bud (s:ℕ)(b:Tower.Field Y H s j 0 true) :
    ∃ f:P.naturalVox j s, α (P.gnsIn j ξ (P.province j ξ s f)) =
      P.greatBud x j s (Selected.admit Y H s j b) := by
  let s₀:= Selected.admit Y H s j b
  have h : P.voxTest j s s₀ ∈ enclave P.calibration :=
    ((purpose_ok ..).1 b.property).2 (Eq.refl _)
  let f:P.naturalVox j s:= ⟨s₀,h⟩
  exact ⟨f, (congrArg α (P.coincides ..)).trans (P.foyer_bud ..)⟩
private lemma surjLift {K L:Hilbert}(V':K.space→ₗᵢ[ℂ]L.space)(p : DenseRange V') : Function.Surjective V' :=
  fun i=> (show i ∈ Set.range V' from V'.isometry.isClosedEmbedding.isClosed_range.closure_eq ▸ p i)
lemma foyer_onto : Function.Surjective (fun i:Hc => α (P.gnsIn j ξ i)) := by
  apply surjLift (K:=Hc) (L:=Hi) ((α).toLinearIsometry.comp (P.gnsIn j ξ))
  apply (Selected.reserved_actor Y H V G Gt j (C j) χ).mono
  rintro i p; obtain ⟨s,b,h⟩ := Set.mem_iUnion.mp p; obtain ⟨f,q⟩ := P.neutral_bud x j s b
  exact ⟨P.province j ξ s f,q.trans h⟩

noncomputable def colorRoom : (P.ColorHil j (P.advocate 3 x j)) ≃ₗᵢ[ℂ] P.GreatRoom x j :=
  LinearIsometryEquiv.ofSurjective ((P.foyer x j).toLinearIsometry.comp (P.gnsIn j ξ)) (P.foyer_onto x j)
local notation "β" => P.colorRoom x j
lemma colorRoom_apply (i:Hc) : β i= α (P.gnsIn j ξ i) := rfl
lemma colorRoom_vacuum : β (P.colorZero j ξ)= Selected.doorstep Y H V G Gt j false (C j) χ := by
  rw [P.colorRoom_apply,P.present0,P.foyer_vacuum]
lemma colorRoom_actor (s:ℕ)(f:P.naturalVox j s) : β (P.province j ξ s f) = Bg s f.1 := by
  rw [P.colorRoom_apply,P.coincides,P.foyer_bud]

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

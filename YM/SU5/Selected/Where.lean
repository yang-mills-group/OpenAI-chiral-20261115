/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Selected.CapSizes
import YM.SU5.Selected.BridgedAxes
import YM.Ground.Spectrum

/-!
# Phase spectrum on the shared axes. Bounded operators from the same history.

Specs: port/instantiation of the general C*-fact from `YM/Ground/Spectrum` (receives_). Nothing
consumed about YM continuum histories/statistical sym. Instantiated over THIS genuine ground
algebra using the Tapestry Fashion.Exhibition over same V and coherence, align by Transfer
(diverging/reordering histories doesn't replace this compactness step).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 650000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (j : Axis) (r : Bool) (C : Arena Y H Q.circuit j 0 r)
local notation "R" => Aurora Y H V Q j r C
local notation "A" => Ark.Ht Y H Q.circuit j 0 r C
local notation "W" => floorV Y H Q.circuit j 0 r C
local notation "F₊" n:max => Tower.Field Y H n j 0 r
local notation "φ" n:max => actor Y H n Q.circuit j 0 r C
local notation "Ω" => seat0 Y H V Q j r C
local notation "π₀" => (R).orthogonalProjectionOnto
local notation "N" n:max => cap Y H V n Q Qc j r C
local notation "Test" => Vacancy.observable (tent Y H) r
local notation "Lab" => Beacon (tent Y H) r

open OS.Ground TopologicalSpace
open Spectral
open scoped ContDiff
local notation "H₀" => basisRoom Y H V Q j r C
local notation "B" => groundAlgebra Y H V Q Qc j r C
local notation "X₀" => (groundAlgebra Y H V Q Qc j r C).subtype
local notation "M" s:max => liftCap Y H V Q Qc j r C s
-- general theorem (proof repeat from Spectrum, see header; implicit arguments tuned if needed)
private lemma obtain_distribution {X : Type} [CommCStarAlgebra X] [SeparableSpace X] (K' : Hilbert)
    (p : X →⋆ₐ[ℂ] K'.Op) (w : K') (hw : ‖w‖=1) (h : ∀ u : X, p u w=0 → u=0) :
    ∃ R' : Panes X, R'.Shines K' p w := by
  classical
  let T := Theta (X := X)
  letI : MetrizableSpace T := tiny (denseSeq X) (denseRange_denseSeq _)
  letI : MetricSpace T := metrizableSpaceMetric T
  letI : MeasurableSpace T := borel _; letI : BorelSpace T := ⟨rfl⟩
  let P : Rep.CC T →⋆ₐ[ℂ] K'.Op := p.comp ((_root_.gelfandStarTransform X).symm : _ →⋆ₐ[ℂ] _)
  let U : Panes X := { X := T, μ := Rep.sees P w, character := view }
  have hp i : P (gelfandStarTransform X i)=p i := congr_arg p ((gelfandStarTransform X).symm_apply_apply _)
  refine ⟨U,?_,?_,bij,view_cont,mark_cont,?_⟩
  · apply isProbabilityMeasure_iff_real.mpr
    change (Rep.sees P w).real _=1
    rw [Rep.size,hw,one_pow]
  · refine supports K' P w ?_
    intro x hx
    obtain ⟨i,rfl⟩ := (gelfandStarTransform X).surjective x
    change P (gelfandStarTransform X i) w=0 at hx; rw [hp] at hx
    change (gelfandStarTransform X i)=0; rw [h i hx,map_zero]
  intro i
  have h' := Rep.pairings P w (gelfandStarTransform X i)
  rw [hp] at h'; exact h'

abbrev Horizon := Panes ↑(B)
abbrev Law (Z : Horizon Y H V Q Qc j r C) := Z.Shines H₀ X₀ Ω
local notation "ZL" => Law Y H V Q Qc j r C
section full
-- no separability widths at true yet
lemma vision (X : Arena Y H Q.circuit j 0 false) {S : Tapestry.Rack Λ l}
    {P : Tapestry.Clay Λ l} (U : Tapestry.Exhibition Y H i k I E S P) :
    ∃ Z : Horizon Y H V Q Qc j false X, Law Y H V Q Qc j false X Z := by
  let B' := groundAlgebra Y H V Q Qc j false X
  let M' : Hilbert := basisRoom Y H V Q j false X
  letI : CommCStarAlgebra B' := spectrumData Y H V Q Qc j false X
  haveI : SeparableSpace B' := small_algebra Y H V Q Qc j X U
  refine obtain_distribution (X:= ↑B') M' (B'.subtype : (B') →⋆ₐ[ℂ] M'.Op) (seat0 Y H V Q j false X)
    (ground_normalized Y H V Q j false X) (fun i => distinguish Y H V Q Qc j false X i 0)
end full

include V Q Qc C
variable (Z : Horizon Y H V Q Qc j r C) (h : Law Y H V Q Qc j r C Z)
include h
lemma many_accept (s : ℕ) (F : Test) :
    Continuous (fun i => marked Y H V Q Qc j r C (Z.character i) s F) ∧
      (∫ i : Z.X, marked Y H V Q Qc j r C (Z.character i) s F ∂Z.μ)=E s F.val :=
  ⟨h.weak ((M s) F), (h.ground ((M s) F)).trans (inspected Y H V s Q Qc j r C)⟩ -- include h below

variable (v : Axis) (C' : Arena Y H Q.circuit v 0 r)
include C'
local notation "Φ" => coincide Y H V Q Qc j r C v C'

def emigrant : Horizon Y H V Q Qc v r C' where
  X := Z.X
  μ := Z.μ
  character x := escort Y H V Q Qc j r C v C' (Z.character x)
-- equivalence char equivalences vanilla
omit V Q Qc C C' h in
private lemma matching (X Y : Type) [Ring X] [StarRing X] [Algebra ℂ X]
    [Ring Y] [StarRing Y] [Algebra ℂ Y] (J : X ≃⋆ₐ[ℂ] Y) : Bijective (fun i : X→⋆ₐ[ℂ] ℂ => i.comp J.symm.toStarAlgHom) := by
  let f (p : Y→⋆ₐ[ℂ] ℂ) := p.comp J.toStarAlgHom
  have p (p : X→⋆ₐ[ℂ] ℂ) : f (p.comp J.symm.toStarAlgHom) = p := by
    refine DFunLike.ext _ _ (fun i=> ?_); exact congrArg p (J.symm_apply_apply _)
  exact ⟨fun i j t => (p i).symm.trans ((congrArg f t).trans (p j)),
    fun i => ⟨f i, DFunLike.ext _ _ (fun x=> congrArg i (J.apply_symm_apply _))⟩⟩
lemma brought : Law Y H V Q Qc v r C' (emigrant Y H V Q Qc j r C Z v C') := by
  refine ⟨h.normalized,h.support, (matching ↑(B) _ (Φ)).comp h.onto,?_, fun i=> h.weak ((Φ).symm i),?_⟩
  · letI := spectrumData Y H V Q Qc j r C; letI := spectrumData Y H V Q Qc v r C'
    exact fun i => (h.values i).comp (StarAlgEquiv.isometry (Φ).symm).continuous
  intro i
  obtain ⟨x,rfl⟩ := (Φ).surjective i
  refine Eq.trans ?_ ((h.ground x).trans (expectations Y H V Q Qc j r C v C' x)); refine congrArg (fun p:Z.X→ℂ=>∫i,p i ∂Z.μ) (funext fun y => ?_)
  exact congrArg (Z.character y) ((Φ).symm_apply_apply _)
end YM.CF.Buffered.Afterglow.Tower.Selection

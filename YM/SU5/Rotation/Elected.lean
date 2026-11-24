import VerifiedSatinOddProbes
import YM.SU5.Rotation.Retesting

/-!
# The obstruction on the very data with the interacting and graded election
-/
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option maxRecDepth 7500
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Scree Window Vale Girt Lifted
open Py Py.Rate LocalLimit Preparation Satin Heat Fock SlabMark PhaseChoice Push.SectorMeasure
open Tapestry Tapestry.Altitude Tapestry.Exhibition
open CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet
open Reliance ShortWave
open Tower.Selected Vacancy
open Journey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra

variable {Λ:Preparation} {l:ℕ} {Y:Course Λ (VolumeCape.Dream.Nimbus l)} {H:Real.exp 1≤Λ.x}
local notation "K" => tent Y H

variable {a b:ℕ→ℕ} {I:ℕ→ Family (tent Y H) → ℕ → ℂ} {E:ℕ→ Family (tent Y H) → ℂ}
    {L:Rack Λ l} {B:Clay Λ l} {T:ℕ→ℕ→Tariff} {t:ℕ→Tariff} {D: Fashion Y H a b I E L B T t}
    {G:SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H}
    {j:Axis} {c:∀ j,Arena Y H G.history.circuit j 0 false}
    {χ: displayAlgebra Y H D.univ_ G.history G.clipped 0 false (c 0) →⋆ₐ[ℂ] ℂ}
    {s:ℕ} {S:Finset Cover} {z:SU.Slot} {u v:ℕ} {o:Cover} {δ w:ℝ} {p q:Cover} {f:Marks (tent Y H) true}

/-- Adapter: the unchanged Coupled witness, from the very `PaidNeighborhoods`
in the conclusion below, in this obstructed system. Separately supported
gauge invariant Mark polynomials (even originally narrow), separation in
physical lengths and still the *same-character* nonzero reading of their product.
Keep `Coupled` itself for the predictor/nonfactorization qualification. -/
theorem Coupled.on_obstructed_algebra
    (r : Coupled Y H D.toExhibition G 0 j c χ s (S:=S) (z:=z) (u:=u) (v:=v) (o:=o)
      (δ:=δ) (w:=w) p q f) :
    let x := pinhole (Dome K) s (PhaseChoice.resolutionProbe Y H
      (mirrorInMarks Y H j true (relocateWorld Y H true p f)))
    let y := pinhole (Dome K) s (PhaseChoice.resolutionProbe Y H (relocateWorld Y H true q f))
    let U₁ := footprint Λ l s (reflectedBox j 0 (streetBox K p S))
    let U₂ := footprint Λ l s (streetBox K q S)
    x∈ Pol Y H U₁ ∧ y∈ Pol Y H U₂ ∧ x*y∈ Pol Y H (U₁∪U₂) ∧
    0<δ ∧ (∀ (i:Axis) a, a∈ U₁ → ∀ b∈ U₂, a i + δ ≤ b i) ∧
    1/32 ≤ ‖(sch Y H D G c χ) (x*y)‖ := by
  intro x y U₁ U₂
  have widen (V : Set RSpace) : circum Λ l K false V {s} ≤ Pol Y H V :=
    (wellWider Λ K l false (handstamp V) {s}).trans (circum_widens Y H Set.Subset.rfl (Set.subset_univ _))
  have h : x∈ Pol Y H U₁ := widen U₁ r.certified.region₁
  have g : y∈ Pol Y H U₂ := widen U₂ r.certified.region₂
  exact ⟨h,g,(Pol Y H (U₁∪U₂)).mul_mem
    (circum_widens Y H Set.subset_union_left Set.Subset.rfl h)
    (circum_widens Y H Set.subset_union_right Set.Subset.rfl g),
    r.certified.delta,r.certified.separatedNonzero,r.certified.prices⟩
end YM.CF.Buffered.Afterglow.Tower.Reconstruction

namespace YM.CF.Py.Rate.LocalLimit.Papal
open Function Set Filter MeasureTheory
open Lattice SU Buffered Afterglow Journey Preparation CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet
open Satin Tapestry Tower Tower.Selected Tower.Vacancy Tower.PhaseChoice
open Tower.Reconstruction
open RotationObstruction
open scoped Topology BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra

universe v

variable {ε η : ℝ} {U:Supplier} {P : Preparation} {l : ℕ} {Z ζ:ℝ} {H : Real.exp 1 ≤ P.x}
    {Y : Course P (VolumeCape.Dream.Nimbus l)} {q d w:ℕ} {C:ℝ}
    {a b : ℕ → ℕ} {I : ℕ → Buffered.Family (tent Y H) → ℕ → ℂ} {E : ℕ → Buffered.Family (tent Y H) → ℂ}
    {L : Rack P l} {B : Tapestry.Clay P l} {T : ℕ → ℕ → Tapestry.Tariff} {t : ℕ → Tapestry.Tariff}
    {D : Tapestry.Fashion Y H a b I E L B T t}
    {G : SatinVerification.GroundExtension (i := a) (k := b) (E := E) Y H}
    {room : ∀ j, Tower.Arena Y H G.history.circuit j 0 false}
    {pan : Panel Y H D.univ_ G.history G.clipped 0 false (room 0)}
    {s : ℕ}
    {f f' : SU.Slot → observable (tent Y H) true} {sample : pan.X}

/-- Can use on *any* such election data. Doesn't even need the Election proof
(or PosSemidef, or interactions) to derive the obstruction. -/
lemma Election.obstruction (_ : Election ε η U P l Z H Y q d w C a b I E L B T t D G room pan s ζ f f' sample) :
    FixedResolutionGap Y H D G room (pan.character sample) :=
  result Y H D G room (pan.character sample)

/-- Public existence endpoint: extend the verified result with the obstruction.
No resetting prices or refinement history; no changing character from sample.
Use `Coupled.on_obstructed_algebra` on any of the Coupled witnesses in the
conclusion to read that signal on `Pol`. `FixedResolutionGap` names the actual
geometry/support/approximation and correlation-continuity claim.
-/
theorem selectedRotationObstructionAlternative (ε η : ℝ) (hη : 0 < η) (U : Supplier) :
    ∃ P l Z H Y q d w C a b I E L B T t D G room pan s ζ f f' sample,
      Election ε η U P l Z H Y q d w C a b I E L B T t D G room pan s ζ f f' sample ∧
      PaidNeighborhoods (D:=D) (G:=G) (room:=room) (pan:=pan) (sample:=sample)
        (s:=s) (ζ:=ζ) (f':=f') (q:=q) (d:=d) (w:=w) ∧
      ElectedGradedProbes.{v} (D:=D) (G:=G) (room:=room) (pan:=pan) (sample:=sample) ∧
      FixedResolutionGap Y H D G room (pan.character sample) := by
  obtain ⟨P,l,Z,H,Y,q,d,w,C,a,b,I,E,L,B,T,t,D,G,room,pan,s,ζ,f,f',sample,e,p,g⟩ :=
    selectedInteractingGradedProbes.{v} ε η hη U
  exact ⟨P,l,Z,H,Y,q,d,w,C,a,b,I,E,L,B,T,t,D,G,room,pan,s,ζ,f,f',sample,e,p,g,
    Election.obstruction e⟩
end YM.CF.Py.Rate.LocalLimit.Papal

#print axioms YM.CF.Py.Rate.LocalLimit.Papal.selectedRotationObstructionAlternative
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.Election.obstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Coupled.on_obstructed_algebra

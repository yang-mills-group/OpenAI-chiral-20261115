import YM.SU5.Selected.Where
import YM.SU5.Selected.Gap
import YM.SU5.Selected.Euro.Plume
import YM.SU5.Selected.Ablate
import YM.SU5.Verified.SatinSameCharacter
import YM.SU5.Reconstruct.Determine

/-! # A *single* character: transfer actual readings to the `Reconstruction` API

No claim securely comparing two choices from different existence theorems.
Use the equivalence here on the SAME data. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection.Home
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Tapestry Tapestry.Altitude
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
section
variable (V:Universal Y H i k I E) {D:ℕ→Family (tent Y H)→Family (tent Y H)} {a b:ℕ→ℕ}
    (Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)(Qc:Clipped Y H (i∘a) (k∘b))
    (j:Axis)(r: Bool)(C : Arena Y H Q.circuit j 0 r)
open Tower.Selected
local notation "P" => groundAlgebra Y H V Q Qc j r C
local notation "B" => displayAlgebra Y H V Q Qc j r C
lemma same_ground : groundAlgebra Y H V Q Qc j r C=displayAlgebra Y H V Q Qc j r C := rfl
/-- Exposing even at the Cap type. -/
abbrev asDisplay (χ:CapCharacter Y H V Q Qc j r C) : displayAlgebra Y H V Q Qc j r C →⋆ₐ[ℂ] ℂ := χ
abbrev asPanel (Ψ:Horizon Y H V Q Qc j r C) : Panel Y H V Q Qc j r C := Ψ
lemma issued (Ψ:Horizon Y H V Q Qc j r C) (p:Law Y H V Q Qc j r C Ψ) : Issued Y H V Q Qc j r C (asPanel Y H V Q Qc j r C Ψ) := p
variable (χ:CapCharacter Y H V Q Qc j r C)
local notation "Ψ" => asDisplay Y H V Q Qc j r C χ
lemma same_call (s:ℕ)(f:Marks K r) : Selection.marked Y H V Q Qc j r C χ s f=Selected.response Y H V s Q Qc j r C Ψ f := rfl

open CStarAlgebra
/-- Any axis, any r, any cap character; enough to test on the actual cap generators. -/
lemma cap_ext (y: displayAlgebra Y H V Q Qc j r C →⋆ₐ[ℂ] ℂ) (x: displayAlgebra Y H V Q Qc j r C →⋆ₐ[ℂ] ℂ)
    (p: ∀ s:ℕ, ∀ f:Selected.Marks (tent Y H) r, Selected.response Y H V s Q Qc j r C x f = Selected.response Y H V s Q Qc j r C y f): x=y:=by
  -- cf. Determine.polynomial_ext. No reliance on a particular χ at d or on the two PVMs matching
  letI : IsSemitopologicalSemiring (Selected.groundRoom Y H V Q j r C).Op:= Selection.groundSemitop Y H V Q j r C
  letI : ContinuousStar (Selected.groundRoom Y H V Q j r C).Op:= Selection.groundStarCont Y H V Q j r C
  let U:= StarAlgHom.equalizer x y; let G := U.map (B).subtype
  have t : B ≤ G := by
    apply StarSubalgebra.topologicalClosure_minimal (StarAlgebra.adjoin_le ?_)
    · suffices e : IsClosed (U : Set (B)) from
        (displayClosed Y H V Q Qc j r C).isClosedEmbedding_subtypeVal.isClosedMap _ e
      exact isClosed_eq (map_continuous x) (map_continuous y)
    rintro z ⟨w,rfl⟩; obtain ⟨n,f⟩:=w
    exact ⟨_,p n f,rfl⟩
  ext1 z
  obtain ⟨w,e,d⟩:= t z.property
  exact (show w=z from Subtype.ext d) ▸ (show x w=y w from e)

variable (v:Axis)(C': Arena Y H Q.circuit v 0 r)
lemma across (f : Marks K r) (s:ℕ) : Selected.response Y H V s Q Qc v r C'
    (asDisplay Y H V Q Qc v r C' (escort Y H V Q Qc j r C v C' χ)) f = marked Y H V Q Qc j r C χ s f :=
  (same_call Y H V Q Qc v r C' (escort Y H V Q Qc j r C v C' χ) s f).symm.trans
    (unchanged Y H V Q Qc j r C v C' χ s f)

/-- No new spectral selection even using the independently-developed chart interface. -/
theorem asDisplay_other : asDisplay Y H V Q Qc v r C' (escort Y H V Q Qc j r C v C' χ) =
    Selected.displacement Y H V Q Qc j r C Ψ v C' := by
  apply cap_ext
  intro i f
  exact (across Y H V Q Qc j r C χ v C' f i).trans ((same_call Y H V Q Qc j r C χ i f).trans
    (Selected.across_response Y H V i Q Qc j r C (Ψ) f v C').symm)
lemma round_trip (l:Axis)(C₀:Arena Y H Q.circuit l 0 r) :
    escort Y H V Q Qc v r C' l C₀ (escort Y H V Q Qc j r C v C' χ)= escort Y H V Q Qc j r C l C₀ χ:= by
  have t(x y:CapCharacter Y H V Q Qc l r C₀)(p:∀ s f, marked Y H V Q Qc l r C₀ x s f=marked Y H V Q Qc l r C₀ y s f): x=y:= cap_ext Y H V Q Qc l r C₀ (asDisplay Y H V Q Qc l r C₀ y) (asDisplay Y H V Q Qc l r C₀ x) p -- defeq
  exact t _ _ (fun i x=>(unchanged Y H V Q Qc v r C' l C₀ _ i x).trans ((unchanged Y H V Q Qc j r C v C' χ i x).trans (unchanged Y H V Q Qc j r C l C₀ χ i x).symm))
@[simp] lemma round_here : escort Y H V Q Qc j r C j C χ=χ := cap_ext Y H V Q Qc j r C Ψ (asDisplay Y H V Q Qc j r C (escort Y H V Q Qc j r C j C χ)) (unchanged Y H V Q Qc j r C j C χ)
end

open Tapestry Tower.Reconstruction Tower.PhaseChoice
variable {L: Rack Λ l} {B:Clay Λ l} {T:ℕ→ℕ→Tariff} {t:ℕ→Tariff} (D: Fashion Y H i k I E L B T t)
    (G:SatinVerification.GroundExtension (i:=i) (k:=k) (E:=E) Y H)
    (C:∀ j:Axis, Arena Y H G.history.circuit j 0 false)
    (j : Axis)
    (χ:CapCharacter Y H D.univ_ G.history G.clipped j false (C j))
local notation "Δ" => Dome (tent Y H)
local notation "V₀" => D.univ_
local notation "Vₑ" => D.toExhibition
local notation "Q" => G.history
local notation "Qt" => G.clipped
local notation "e" v:max => escort Y H V₀ Q Qt j false (C j) v (C v) χ
-- give simple abbreviation wrapper
abbrev dial (v:Axis) : Tower.Selected.displayAlgebra Y H D.univ_ G.history G.clipped v false (C v) →⋆ₐ[ℂ] ℂ:=
   asDisplay Y H V₀ Q Qt v false (C v) (e v)
local notation "d" v:max => dial Y H D G C j χ v
abbrev reception (v:Axis) := SameCharacter.resident Y H V₀ G v false (C v) (dial Y H D G C j χ v)
lemma resident_at (v:Axis)(s:ℕ)(f:Dome (tent Y H)) : Selection.phaseRead Y H V₀ Q Qt j (C j) χ s f.val = PhaseChoice.evaluate Y H V₀ G v C (reception Y H D G C j χ v) s f.val :=
  let w:=fieldArg Y H f
  (phase_read Y H V₀ Q Qt j (C j) s χ w).trans ((across Y H V₀ Q Qt j false (C j) χ v (C v) w s).symm.trans ((evaluates Y H V₀ G v C (reception Y H D G C j χ v) s w).trans (SameCharacter.sameReading Y H V₀ G v false (C v) (d v) s w)).symm)
local notation "Γ" => sch Y H D G C (d 0)
lemma sch_phase (s:ℕ){x:Altitude.Cloud (Dome (tent Y H))}(p:x∈boardedDB K s) :
    sch Y H D G C (d 0) x = phaseRead Y H V₀ Q Qt j (C j) χ s ((Vₑ).vistaFinish Y H s x).val:= by
  let f := Reconstruction.fieldArg Y H ((Vₑ).vistaFinish Y H s x)
  exact (Reconstruction.sch_mark Y H D G C (d 0) s p).trans ((across Y H V₀ Q Qt j false (C j) χ 0 (C 0) f s).trans (phase_read Y H V₀ Q Qt j (C j) s χ f).symm)
lemma sch_selected (s:ℕ){x:Altitude.Cloud Δ}(p:x∈boardedDB K s) :
    (Γ) x = Selection.bill Y H V₀ Q Qt j (C j) (Vₑ) χ x :=
  let f := Reconstruction.fieldArg Y H ((Vₑ).vistaFinish Y H s x)
  (Reconstruction.sch_mark Y H D G C (d 0) s p).trans ((across Y H V₀ Q Qt j false (C j) χ 0 (C 0) f s).trans
    (cardHeight Y H V₀ Q Qt j (C j) (Vₑ) χ s p).symm)
lemma sch_hole (s:ℕ)(f:Δ) : (Γ) (pinhole Δ s f)= phaseRead Y H V₀ Q Qt j (C j) χ s f.val:=
   (sch_sample Y H D G C (d 0) s f).trans ((across Y H V₀ Q Qt j false (C j) χ 0 (C 0) (fieldArg Y H f) s).trans (phase_read Y H V₀ Q Qt j (C j) s χ (fieldArg Y H f)).symm)
lemma asDisplay_chosen (u v:Axis) : Selected.displacement Y H V₀ Q Qt u false (C u) (dial Y H D G C j χ u) v (C v)=dial Y H D G C j χ v:=
  (asDisplay_other Y H V₀ Q Qt u false (C u) (e u) v (C v)).symm.trans (round_trip Y H V₀ Q Qt j false (C j) χ u (C u) v (C v))
end YM.CF.Buffered.Afterglow.Tower.Selection.Home
open YM.CF.Buffered.Afterglow.Tower.Selection.Home
#print axioms asDisplay_chosen
#print axioms sch_selected
#print axioms same_ground
#print axioms resident_at
#print axioms cap_ext
#print axioms YM.CF.Buffered.Afterglow.Tower.Selection.Home.issued
#print axioms round_here

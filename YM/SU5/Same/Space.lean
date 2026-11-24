import SU5SatinVerifiedNovember6

/-!
# Same-character identification (CP18 vs CP27), I

This module and the subsequent `YM.SU5.Same` modules use the **public entry**
without any changes to the hypotheses/storage of the named physical statements.

For any Spine, axis and character we identify the CP18 ColorHil with the
*whole* CP27 `indoor` Hilbert space (not just its spatially continuous part)
in that consultation. `indoor` is the possibly-larger-looking loose Mark GNS system.
This buys the transport of the CP18 *field-ket convergences*, including study
of extrapolation to zero heat, to the CP27 space where one must verify boost and
registration estimates on the very marks. It also lets us work in either
system towards those estimates without paying them first to identify limiting
operators or vacua.

Here the axis-a reference character is given once. Move that one and not the
marks across axes, and also in `a` itself use exactly the prescribed CP18/CP27
moves (`advocate`/`displacement`). We do not identify the Hilbert spaces of
different axes as though this were already continuous rotation covariant.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 4000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine

variable (P : Spine) (a : Axis) (x : P.Spectrum0 a) (j : Axis)
local notation "Y" => P.run
local notation "H" => P.large
local notation "V" => P.law
local notation "G" => P.projection

/-- The actual CP27 displacement of the display of the reference CP18 character. -/
abbrev glassAxis := Selected.displacement P.run P.large P.law
  P.history P.projection.clipped a false (P.room a) (P.glasshouseCharacter a x) j (P.room j)

local notation "c" => P.glassAxis a x j
local notation "ξ" => P.advocate a x j

abbrev glassSpace : Hilbert := Selected.indoor Y H V P.history
  P.projection.clipped j false (P.room j) (P.glassAxis a x j)
abbrev glassVac : (P.glassSpace a x j) := Selected.doorstep Y H V P.history
  P.projection.clipped j false (P.room j) (P.glassAxis a x j)
local notation "R" => P.glassSpace a x j
local notation "S" => P.ColorHil j ξ

variable (s t : ℕ)

lemma glassAxis_response (f : P.Test) : Selected.response Y H V s P.history P.projection.clipped
    j false (P.room j) (P.glassAxis a x j) (P.glasshouseMark f) = P.singleState j s (P.advocate a x j) f := by
  calc
    _ = Selected.response Y H V s P.history P.projection.clipped a false (P.room a)
        (P.glasshouseCharacter a x) (P.glasshouseMark f) :=
      Selected.across_response Y H V s P.history P.projection.clipped a false (P.room a)
        (P.glasshouseCharacter a x) (P.glasshouseMark f) j (P.room j)
    _ = P.singleState a s x f := rfl
    _ = _ := (P.single_agrees a j x s f).symm

/-- Same positive-time test with its loose Field qualification. -/
abbrev bornVox {f : P.Test} (p : P.birthF j s f) : P.Vox j s :=
  ⟨f.val, (show f.val ∈ purpose P.calibration (meshface (Λ:=P.par) 0 s) j false from by
    obtain ⟨w,rfl⟩ := p
    exact w.val.property)⟩

/-- Field support at axis `j` in physical (level-zero *matter*) length units,
with the strict Mark qualification. Note `flank` uses `≥`.
CP18 body/seam tests will give the *actual* pair of boxes as well. -/
theorem birthF_iff_glass (f : P.Test) : P.birthF j s f ↔
    f ∈ FirstWindows.insideAt P.par P.width P.calibration true (flank j 0) s := by
  rw [FirstWindows.positive_today, purpose_ok]
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨((purpose_ok ..).1 g.val.property).1, fun _ => g.property⟩
  rintro ⟨h, t⟩
  exact ⟨⟨⟨f.val, (purpose_ok ..).2 ⟨h, nofun⟩⟩, t rfl⟩, rfl⟩

/-- The ket of the same birth mark in CP27. -/
abbrev glassBud {f : P.Test} (p : P.birthF j s f) : R :=
  Selected.bud Y H V s P.history P.projection.clipped j false (P.room j) (P.glassAxis a x j) (P.bornVox j s p)

/-- It really is the physicalket of the ticket (strict singlets Domain). -/
theorem glassBud_physicalKet {f : P.Test} (p : P.birthF j s f) :
    P.glassBud a x j s p = FirstWindows.physicalKet Y H V G j (P.room j) c
      (FirstWindows.enclose Y H G (flank j 0) true s ⟨f, (P.birthF_iff_glass j s f).1 p⟩) := by
  rw [FirstWindows.physical_enclose]
  rfl

theorem glassGram_same_height {f g : P.Test} (p : P.birthF j s f) (q : P.birthF j s g) :
    inner ℂ (P.viewF j ξ s p) (P.viewF j ξ s q) =
      inner ℂ (P.glassBud a x j s p) (P.glassBud a x j s q) := by
  rw [P.released_gram, ← P.glassAxis_response]
  exact (Selected.earns Y H V s P.history P.projection.clipped j false (P.room j) c
    (P.bornVox j s p) (P.bornVox j s q)).symm

lemma glassBud_promote {f : P.Test} (p : P.birthF j s f) (e : s ≤ t) :
    P.glassBud a x j t (P.rig j s t p e) = P.glassBud a x j s p :=
  Selected.flourishes Y H V s P.history P.projection.clipped j false (P.room j) c t e (P.bornVox j s p)

/-- Works before even aligning the mark heights. -/
theorem glassGram {f g : P.Test} (p : P.birthF j s f) (q : P.birthF j t g) :
    inner ℂ (P.viewF j ξ s p) (P.viewF j ξ t q) =
      inner ℂ (P.glassBud a x j s p) (P.glassBud a x j t q) := by
  let e := le_max_left s t
  let v := le_max_right s t
  calc
    _ = inner ℂ (P.viewF j ξ _ (P.rig j s (max s t) p e))
        (P.viewF j ξ _ (P.rig j t (max s t) q v)) :=
      congrArg₂ (inner ℂ) (P.view_rig j ξ s _ p e).symm (P.view_rig j ξ t _ q v).symm
    _ = _ := (P.glassGram_same_height a x j _ (P.rig j s (max s t) p e)
        (P.rig j t (max s t) q v)).trans (congrArg₂ (inner ℂ)
          (P.glassBud_promote a x j s _ p e) (P.glassBud_promote a x j t _ q v))

def glassPartner (u : P.Partner j) := P.glassBud a x j u.1 u.2.property

/-- Density using the *singlet* marks of the same calibration. -/
theorem glassPartner_dense : DenseRange (P.glassPartner a x j) := by
  apply (Selected.reserved_actor Y H V P.history P.projection.clipped j (P.room j) c).mono
  intro u p
  obtain ⟨s,h⟩ := Set.mem_iUnion.mp p
  obtain ⟨f,rfl⟩ := h
  let g := P.voxTest j s (Selected.admit Y H s j f)
  have h : P.birthF j s g := ⟨⟨Selected.admit Y H s j f, ((purpose_ok ..).1 f.property).2 rfl⟩, rfl⟩
  exact ⟨⟨s,g,h⟩,rfl⟩

private theorem exists_toGlass :
    ∃ y : S ≃ₗᵢ[ℂ] R, ∀ u : P.Partner j, y (P.oneSide j ξ u) = P.glassPartner a x j u :=
  intertwine (A:=S) (B:=R) _ _ (P.partner_dense j ξ)
    ((P.glassPartner_dense a x j).mono Submodule.subset_span) (fun u v =>
      P.glassGram a x j u.1 v.1 u.2.property v.2.property)

/-- Identify the Hilbert spaces without changing axis, selected vacuum, or support.
Full, not just on the subspace with continuous transverse translations. -/
noncomputable def toGlass : P.ColorHil j (P.advocate a x j) ≃ₗᵢ[ℂ] P.glassSpace a x j :=
  (P.exists_toGlass a x j).choose

lemma toGlass_view {f : P.Test} (p : P.birthF j s f) :
    P.toGlass a x j (P.viewF j ξ s p) = P.glassBud a x j s p :=
  (P.exists_toGlass a x j).choose_spec ⟨s, f, p⟩

lemma toGlass_vacuum : P.toGlass a x j (P.colorZero j (P.advocate a x j)) = P.glassVac a x j := by
  rw [← P.view_one j ξ 0, P.toGlass_view]
  exact Selected.root Y H V 0 P.history P.projection.clipped j false (P.room j) c

#print axioms glassBud_physicalKet
#print axioms toGlass_view
#print axioms toGlass_vacuum
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

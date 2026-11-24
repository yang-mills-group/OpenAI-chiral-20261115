import SatinGlasshouseReadingNovember6
import YM.SU5.Twilight.Directions
import YM.SU5.Aria.Trellis
import YM.SU5.Reconstruction.FirstWindows.Half

/-!
# Registration project, CP1.  Buy the Hilbert identification, then the
Euclidean **operator** part of registration of the mixed fixed probes.

This file: on the very same Character and Spine, in *every* orientation,
unify the two selected full Hilbert spaces in the question. The arena in
the BoostBacking hypothesis is not to be reselected to produce this. We
can't just rewrite the character: reconstruction from the other's
response, Gram isometry, and whole-Hilbert extensions matter (including
for localization prices in different axes).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 480000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
namespace Spine

open Aria Germ Alliance SelectionAnalysis Set
variable (P : Spine) (x : P.Spectrum0 3) (j : Axis)
local notation "C" => P.room
local notation "Y" => P.run
local notation "L" => P.large
local notation "P₁" => P.par
local notation "V" => P.law
local notation "G" => P.projection
local notation "H" => P.history
local notation "H₁" => P.projection.clipped
abbrev mayChar := Selected.displacement Y L V H H₁ 3 false (C 3)
  (P.glasshouseCharacter 3 x) j (C j)
abbrev mayHil := Selected.indoor Y L V H H₁ j false (C j) (P.mayChar x j)
local notation "χ" => P.mayChar x j
local notation "I₀" => P.mayHil x j
local notation "J" => P.advocate 3 x j
local notation "X" => P.ColorHil j J
local notation "B" s:max f:max => Selected.bud Y L V s H H₁ j false (C j) χ f
local notation "Ω" => Selected.doorstep Y L V H H₁ j false (C j) χ
local notation "Ωₓ" => P.colorZero j J

lemma mayResponse (s : ℕ) (f : P.Test) :
    Selected.response Y L V s H H₁ j false (C j) χ (P.glasshouseMark f) = P.singleState 3 s x f :=
  (Selected.across_response Y L V s H H₁ 3 false (C 3) (P.glasshouseCharacter 3 x)
    (P.glasshouseMark f) j (C j)).trans (P.glasshouseResponse_eq 3 x s f)

lemma mayResponse_advocate (s : ℕ) (f : P.Test) :
    Selected.response Y L V s H H₁ j false (C j) χ (P.glasshouseMark f) = P.singleState j s J f :=
  (P.mayResponse x j s f).trans (P.single_agrees 3 j x s f).symm

lemma may_same_gram (s : ℕ) (f g : P.naturalVox j s) :
    inner ℂ (B s f.val) (B s g.val) = inner ℂ (P.province j J s f) (P.province j J s g) := by
  rw [←(P.gnsIn j J).inner_map_map (P.province j J s f), P.coincides, P.coincides, P.gram_at]
  rw [Selected.earns]
  exact P.mayResponse_advocate x j s (P.reflectTest j (P.voxTest j s f.val) * P.voxTest j s g.val)

def mayRaised {s t : ℕ} (h : s ≤ t) (f : P.naturalVox j s) : P.naturalVox j t :=
  ⟨Raise Y L (H).circuit j 0 false s t h f.val,P.refine_keeps s _ f.property (t-s)⟩
lemma mayProvince_raise {s t : ℕ} (h : s ≤ t) (f : P.naturalVox j s) :
    P.province j J t (P.mayRaised j h f) = P.province j J s f := by
  apply (P.gnsIn j J).injective
  rw [P.coincides, P.coincides]
  exact P.refine_vox j J s t h _
lemma mayBud_raise {s t : ℕ} (h : s ≤ t) (f : P.naturalVox j s) :
    B t (P.mayRaised j h f).val = B s f.val :=
  Selected.flourishes Y L V s H H₁ j false (C j) χ t h _

abbrev MayVox := Σ s, P.naturalVox j s
abbrev mayRoot (v : P.MayVox j) := P.province j J v.1 v.2
abbrev mayBud (v : P.MayVox j) := B (v.1) v.2.val
lemma maySpan : Dense (Submodule.span ℂ (Set.range (P.mayRoot x j)) : Set X) := by
  apply (P.native_dense j J).mono
  change P.colorSpan j J ≤ Submodule.span ℂ (Set.range (P.mayRoot x j)); apply Submodule.span_mono
  intro v hv
  obtain ⟨s,f,rfl⟩ := Set.mem_iUnion.mp hv
  exact ⟨⟨s,f⟩, rfl⟩
lemma maySpanBud : Dense (Submodule.span ℂ (Set.range (P.mayBud x j)) : Set I₀) := by
  apply (Selected.reserved_actor Y L V H H₁ j (C j) χ).mono
  intro v hv; obtain ⟨s,f,rfl⟩ := Set.mem_iUnion.mp hv
  apply Submodule.subset_span
  let g := Selected.admit Y L s j f; let a : P.naturalVox j s := ⟨g,
    by exact ((purpose_ok ..).1 f.property).2 rfl⟩
  exact ⟨⟨s, a⟩, rfl⟩

lemma mayBudget : ∃ U : P.ColorHil j J ≃ₗᵢ[ℂ] P.mayHil x j, ∀ v : P.MayVox j,
    U (P.mayRoot x j v) = P.mayBud x j v := by
  apply intertwine (P.mayRoot x j) (P.mayBud x j) (P.maySpan x j) (P.maySpanBud x j)
  rintro ⟨s,f⟩ ⟨t,g⟩; change inner ℂ (P.province j J s f) (P.province j J t g) = inner ℂ (B s f.val) (B t g.val)
  rw [←P.mayBud_raise x j (le_max_left s t) f, ←P.mayBud_raise x j (le_max_right s t) g,
    ←P.mayProvince_raise x j (le_max_left s t) f, ←P.mayProvince_raise x j (le_max_right s t) g]
  exact (P.may_same_gram x j (max s t) _ _).symm

noncomputable def mayIntertwine : X ≃ₗᵢ[ℂ] I₀ := (P.mayBudget x j).choose
local notation "Uₓ" => P.mayIntertwine x j
lemma mayIntertwine_actor (s : ℕ) (f : P.naturalVox j s) :
    Uₓ (P.province j J s f) = B s f.val := (P.mayBudget x j).choose_spec ⟨s,f⟩
lemma mayVacuum : Uₓ Ωₓ = Ω := by
  rw [←P.identified0, P.mayIntertwine_actor]; exact Selected.root Y L V 0 H H₁ j false (C j) χ

open FirstWindows (Sky ticket enclose Domain domain_one positive_today insideAt OSvector)
local notation "F₊" => FirstWindows.Domain Y L G true (flank j 0)
local notation "F₀" => FirstWindows.Domain Y L G false (flank j 0)
local notation "k" => OSvector Y L V G j (C j) χ
local notation "k'" => FirstWindows.physicalKet Y L V G j (C j) χ
lemma mayInside_loose (s : ℕ) (f : P.Test) (h : P.birthF j s f) :
    f ∈ insideAt P.par P.width P.calibration false (flank j 0) s := by
  obtain ⟨f,rfl⟩ := h; exact (positive_today Y L j s _).2 f.val.property
lemma mayInside (s : ℕ) (f : P.Test) (h : P.birthF j s f) :
    f ∈ insideAt P.par P.width P.calibration true (flank j 0) s := by
  obtain ⟨f,rfl⟩ := h
  simp only [insideAt, ↓reduceIte]
  have he:= P.mayInside_loose j s (P.voxTest j s f.val) ⟨f,rfl⟩
  simp only [insideAt, Bool.false_eq_true, ↓reduceIte, inf_top_eq] at he
  exact ⟨he, f.property⟩
abbrev mayTicket (s : ℕ) (f : P.Test) (h : P.birthF j s f) : F₊ :=
  enclose Y L G (flank j 0) true s ⟨f,P.mayInside j s f h⟩
lemma mayPrice (s : ℕ) (f : P.Test) (h : P.birthF j s f) :
    Uₓ (P.viewF j J s h) = k' (P.mayTicket j s f h) := by
  obtain ⟨f,rfl⟩ := h
  rw [P.holdsF j J s _ f rfl, mayTicket, FirstWindows.physical_enclose, P.mayIntertwine_actor]
  rfl

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

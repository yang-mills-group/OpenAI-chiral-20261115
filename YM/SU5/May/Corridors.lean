import YM.SU5.May.RegistrationBase
import SatinThinQuizMargin
import YM.SU5.Reconstruction.Chambers.PackPair
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
local notation "χ" => P.mayChar x j
local notation "I₀" => P.mayHil x j
local notation "J" => P.advocate 3 x j
local notation "X" => P.ColorHil j J
local notation "Ω" => Selected.doorstep Y L V H H₁ j false (C j) χ
local notation "Ωₓ" => P.colorZero j J

/-!
# CP1 supports & schedules. Pick a *single* pair of strictly inside compact
axis boxes for the shutters of the WHOLE registration problem for this
particular fixed experiment. Keep all-consultation permits eventually.
-/
open DoseTravel MacroGrid SatinNucleus SatinJets
open FirstWindows FirstWindows.Chambers
local notation "ℳ" => marks (timeMesh P.par)
structure MayBooth (F : SampleDose) (B : Doorway) where
  low : Axis → ℳ
  high : Axis → ℳ
  enough (i : Axis) : (low i:ℝ)<(high i:ℝ)
  insideMin (i : Axis) : B.lower i < (low i:ℝ)
  insideMax (i : Axis) : (high i:ℝ) < B.upper i
  ticket (i : Axis) (p : Vantage) (h:p∈tsupport F.val) : (low i:ℝ) < p i ∧ p i < (high i:ℝ)

namespace MayBooth
variable {P} {F: SampleDose} {B : Doorway} (C' : P.MayBooth F B)
def box : Doorway := ⟨fun i=> (C'.low i:ℝ), fun i=> (C'.high i:ℝ), C'.enough⟩
abbrev width (j:Axis) : ℳ := C'.high j - C'.low j
lemma pass : tsupport F.val ⊆ C'.box.invites := fun p h i _=> C'.ticket i p h
lemma housed : C'.box.sealing ⊆ B.invites := fun _ h i _=> ⟨lt_of_lt_of_le (C'.insideMin i) (h.1 i),
    lt_of_le_of_lt (h.2 i) (C'.insideMax i)⟩
-- the Time width in j, all orientations. Used verbatim for queries
lemma allowance : 0 < (C'.width j:ℝ) := sub_pos.mpr (C'.enough j)
lemma prints : C'.box.sealing ⊆ Chambers.strip j (C'.low j) ((C'.low j:ℝ)+(C'.width j:ℝ)):= by
  intro w t; change ↑(C'.low j)≤w j ∧ w j ≤ (C'.low j:ℝ)+((C'.high j:ℝ)-(C'.low j:ℝ)); exact ⟨t.1 j, (t.2 j).trans_eq (by unfold box; dsimp; ring)⟩
variable (P F B) in
lemma choose (h : F.Normalized)(v: tsupport F.val ⊆ B.invites) : Nonempty (P.MayBooth F B) := by
  have z:= dose_visible _ h
  choose f p q using (fun i:Axis=> F.budget.exists_isMaxOn z (continuous_apply i).continuousOn)
  choose b e t using (fun i:Axis=> F.budget.exists_isMinOn z (continuous_apply i).continuousOn)
  choose a h0 x using (fun i:Axis=> Schedule.walls (daylight (timeMesh P.par)) ((v (e i)) i (Set.mem_univ i)).1)
  choose w y g0 using (fun i:Axis=> Schedule.walls (daylight (timeMesh P.par)) ((v (p i)) i (Set.mem_univ i)).2)
  exact ⟨⟨a,w,fun i=> (lt_of_lt_of_le (x i) (t i (p i))).trans (y i),h0,g0,fun i _ m=>
    ⟨lt_of_lt_of_le (x i) (t i m),lt_of_le_of_lt (q i m) (y i)⟩⟩⟩

lemma permits (Y' : ℕ→ P.Apron) (p:P.thicknessZero Y') : ∀ᶠ i in atTop,
    P.spacePrice (Y' i) F ⊆ C'.box.sealing :=
  (P.thin_inside Y' p C'.box.invites C'.box.doorOpen F C'.pass).mono fun i h=>
    h.trans (C'.box.doorSeal ▸ subset_closure)
end MayBooth

lemma footprintPins {S:Finset Cover}{W:Set Vantage}{t:ℕ} (h:P.pinFoot t S ⊆ W): PhaseChoice.SupportedPhysically P.par P.width t S W:=by
  rw [P.usual_footprint] at h; intro x p; exact Set.Subset.trans (Tower.Reconstruction.has_footprint P.par P.width t S x p) (Set.preimage_mono h)

variable (F U:SampleDose) (D : P.MayBooth F reviewEarlierBox) (E : P.MayBooth U reviewLaterBox)
-- compact *physical* schedule separated strictly. Can register these actual amounts.
lemma booths_gap : (D.high j:ℝ)+2 < (E.low j:ℝ) := by
  have h : (D.high j:ℝ) < -1 := D.insideMax j; have u : 1 < (E.low j:ℝ) := E.insideMin j; linarith
lemma booths_disjoint : Disjoint D.box.sealing E.box.sealing := by
  apply Set.disjoint_left.mpr; intro p h e
  have l : p (3:Axis) ≤ (D.high 3:ℝ) := h.2 3
  have h : (E.low 3:ℝ) ≤ p 3:= e.1 _; linarith only [P.booths_gap (3:Axis) F U D E,l,h]
-- pure back (always before by a full width)
noncomputable def boothPair : SpaceFor P.par D.box.sealing E.box.sealing where
  registerQ := ⟨duet D.low E.low, duet D.width E.width,fun i=> by
    intro j; cases i; exact D.allowance j; exact E.allowance j⟩
  back j := eject j (D.low j-D.width j)
  printed j i := by cases i; exact D.prints j; exact E.prints j
  zero_fits := by
    intro i; refine ⟨?_,⟨?_,trivial⟩⟩
    · simp only [↓reduceIte, Schedule.Fixture.start, Schedule.Fixture.paste, Pi.sub_apply, Pi.add_apply, Pi.zero_apply,
        duet_first, Pi.single_eq_same, eject_at, AddSubgroup.coe_sub, zero_add]
      simp only [sub_sub_self]; exact D.allowance i
    simp only [↓reduceIte, Schedule.Fixture.start, Schedule.Fixture.stop, Schedule.Fixture.paste,
      Pi.sub_apply, Pi.add_apply, Pi.zero_apply, duet_first, duet_second, Pi.single_eq_same, eject_at, zero_add]
    change 0 < E.low i-( (D.low i:ℝ)+((D.high i:ℝ)-(D.low i:ℝ)))
    linarith [P.booths_gap i F U D E]

lemma booth_admitted {t:ℕ}{A:P.Apron}{F:SampleDose}{B:Set Vantage} (y : P.spacePrice A F ⊆ B) (p:A.s ≤ t) :
    P.prepared t A F∈ insideAt P.par P.width P.calibration true B t := by
  obtain ⟨S,h,b⟩ := P.prepared_at t A F p
  exact (mem_insideAt (P.prepared t A F) t).2 ⟨⟨S,(Tapestry.locates ..).1 h, P.footprintPins (b.trans y)⟩,
    fun _=> P.prepared_color t A F⟩

variable (A:ℕ → P.Apron) (c r n:ℕ→ℕ) (w:Lead.Clan→ Prism)
  (V':∀ j:Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j))
  (g h:ℕ) (T : P.HandleWith x c r A n) {K:P.Register} {s k:ℕ} {μ:ℝ}
local notation "W'" => P.soldTrumpet A c r n w
local notation "t!" i:max => c (n i)
-- in the ONE pair of these cabins all the stamps in 36 channels and all time orientations pay.
lemma fullPrism_cabin (B' : P.FullPrismLab x A c r n w V' g h T μ F U reviewEarlierBox reviewLaterBox s k K) :
  ∀ᶠ i in atTop, ∀ a:Lead.Clan,
    P.spacePrice ((W' a i).kiss P 3) F ⊆ D.box.sealing ∧ P.spacePrice (W' a i) U ⊆ E.box.sealing := by
  refine eventually_all.mpr fun a => ?_
  exact (MayBooth.permits D (fun i=> (W' a i).kiss P 3) (P.invertWidth _ (B'.armada.slender a))).and
    (MayBooth.permits E (W' a) (B'.armada.slender a))

lemma fullPrism_admitted (B' : P.FullPrismLab x A c r n w V' g h T μ F U reviewEarlierBox reviewLaterBox s k K) :
  ∀ᶠ i in atTop, ∀ t:ℕ, t! i ≤ t → ∀ a:Lead.Clan,
    P.prepared t ((W' a i).kiss P 3) F∈ insideAt P.par P.width P.calibration true D.box.sealing t ∧
    P.prepared t (W' a i) U∈ insideAt P.par P.width P.calibration true E.box.sealing t := by
  refine (P.fullPrism_cabin x F U D E A c r n w V' g h T B').mono fun i e t p a=>
    ⟨P.booth_admitted (e a).1 p,P.booth_admitted (e a).2 p⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

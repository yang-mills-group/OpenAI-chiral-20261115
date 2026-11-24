import YM.Sextet.WallLimit
import YM.SU5.Selected.Upstage
/-!
# Implementation of As for real-valued weights in the transport theorem
Meaning and qualification at single height.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open PhaseChoice (handstamp circum)

/-- Closed center support past the wall, i.e., *earlier* than it, including price `d`. -/
def BeforeWall (j:Axis) (d c:ℝ) (f:Vantage→ℝ) : Prop :=
  ∀ y∈tsupport f, y j + d < c

/-- Closed center support later than the wall, including price `d`. -/
def AfterWall (j:Axis) (d c:ℝ) (f:Vantage→ℝ) : Prop :=
  ∀ y∈tsupport f, c < y j - d

section Footprint
variable (P:Spine) (A B:P.Apron) (f g:Vantage→ℝ)

lemma footBill_bounds {y z:Vantage} (q:z∈P.footBill A y) (j:Axis) :
    y j-A.realWidth P j≤z j ∧ z j≤y j+A.realWidth P j := by
  obtain ⟨u,v⟩:=abs_le.mp (q j); constructor <;> linarith

/-- Footprint union charged for this probe. Coordinates *not doubled*. -/
def poseLayer := {z | ∃ y∈tsupport f,z∈P.footBill A y}

lemma poseLayer_compact (h:HasCompactSupport f) : IsCompact (P.poseLayer A f) := by
  let D:Vantage:=A.realWidth P
  have t:P.poseLayer A f=(fun p:Vantage×Vantage=>p.1+p.2) '' (tsupport f ×ˢ (Set.Icc (-D) D)) := by
    ext x
    constructor
    · rintro ⟨y,g,p⟩
      refine ⟨(y,x-y),⟨g,fun j=>(abs_le.mp (p j)).1,fun j=>(abs_le.mp (p j)).2⟩, add_sub_cancel _ _⟩
    rintro ⟨⟨y,z⟩,⟨p,g,r⟩,rfl⟩
    refine ⟨y,p, fun j=>?_⟩
    change |y j+z j-y j|≤D j
    rw [add_sub_cancel_left]
    exact abs_le.mpr ⟨g j,r j⟩
  exact t.symm ▸ (IsCompact.prod h isCompact_Icc).image (continuous_fst.add continuous_snd)

lemma poseLayer_before {j:Axis}{c:ℝ} (h:BeforeWall j (A.realWidth P j) c f) :
    ∀z∈P.poseLayer A f,z j < c := by
  rintro z ⟨y,q,k⟩; exact (P.footBill_bounds A k j).2.trans_lt (h y q)

lemma poseLayer_after {j:Axis}{c:ℝ} (h:AfterWall j (A.realWidth P j) c f) :
    ∀z∈P.poseLayer A f,c < z j := by
  rintro z ⟨y,q,k⟩; exact (h y q).trans_le (P.footBill_bounds A k j).1

theorem poseLayer_separates {j:Axis}{c:ℝ}
    (u:BeforeWall j (A.realWidth P j) c f) (v:AfterWall j (B.realWidth P j) c g) :
    Disjoint (P.poseLayer A f) (P.poseLayer B g) :=
  Set.disjoint_left.mpr fun _ p q=>(P.poseLayer_before A f u _ p).not_ge
     (P.poseLayer_after B g v _ q).le
end Footprint

section GridFees
open YM.Sextet.Quadrature
variable (P:Spine) (t:ℕ) {f:Vantage→ℝ}

def fineSites (h:HasCompactSupport f) : Finset Cover :=
  (stamp _ h (P.macroTick_pos t)).toFinset

lemma fine_mem (h:HasCompactSupport f) (q:Cover) :
    q∈P.fineSites t h ↔ P.grid t q ∈tsupport f := by
  rw [P.grid_node]
  exact Set.Finite.mem_toFinset _

lemma fine_mem_of (h:HasCompactSupport f) {q:Cover} (b:f (P.grid t q) ≠ 0) :
    q∈P.fineSites t h :=
  (P.fine_mem t h q).mpr (subset_closure b)

variable {U:Type*} [AddCommMonoid U] [Module ℂ U]
lemma fine_counts (h:HasCompactSupport f) (u:Cover→ U) :
    support (fun q=> (f (P.grid t q):ℂ) • u q) ⊆ ↑(P.fineSites t h) := by
  intro q b
  refine P.fine_mem_of t h (fun e=> b ?_)
  change (f (P.grid t q):ℂ) • u q = 0; simp [e]
lemma fine_finite (h:HasCompactSupport f) (u:Cover→ U) :
    HasFiniteSupport (fun q=> (f (P.grid t q):ℂ) • u q) :=
  (Finset.finite_toSet _).subset (P.fine_counts t h u)
lemma fine_sum (h:HasCompactSupport f) (u:Cover→ U) :
    (∑ᶠ q, (f (P.grid t q):ℂ) • u q) = ∑ q∈P.fineSites t h, (f (P.grid t q):ℂ) • u q :=
  finsum_eq_sum_of_support_subset _ (P.fine_counts t h u)
end GridFees

section Purchases
variable (P:Spine) (A:P.Apron) (t:ℕ) (f:Vantage→ℝ)
local notation "h₄" => (((P.macroTick t)^4:ℝ):ℂ)

/-- Resolution test in Eq. `eq:As`, real f, same for reflected poses with
`f` in charge of the poses **as arrived**. Require compact support for `∑ᶠ`.
These use full P-history advances even when asking at extremely large refinement;
no extra ascender price to continue a jitter. -/
def paintMark := h₄ • ∑ᶠ q, (f (P.grid t q):ℂ) • P.aimMark A t q

lemma paint_singlet (h:HasCompactSupport f) : P.paintMark A t f∈enclave P.calibration := by
  rw [paintMark,P.fine_sum t h]
  exact Subalgebra.smul_mem _ (Subalgebra.sum_mem _ (fun i _=>
    Subalgebra.smul_mem _ (P.aim_singlet _ _ _) _)) _

theorem paint_support (R:P.Register) (s:A.s ≤ t) (h:HasCompactSupport f) {V:Set Vantage}
    (u:P.poseLayer A f ⊆ V) :
    P.paintMark A t f ∈ keep P.par P.width t P.calibration true (handstamp V) := by
  rw [paintMark,P.fine_sum t h]
  refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ (fun i hi=>Subalgebra.smul_mem _ ?_ _)) _
  refine rooms _ _ _ _ _ _ ?_ (P.aim_support R A t s i)
  rw [scenery_bill]
  exact fun z a=>u ⟨_, (P.fine_mem t h _).mp hi, a⟩

def paintPoly := Altitude.pinhole P.Test t (P.paintMark A t f)

theorem paint_well (R:P.Register) (s:A.s ≤ t) (h:HasCompactSupport f) {V:Set Vantage}
    (u:P.poseLayer A f ⊆ V) :
    P.paintPoly A t f ∈ circum P.par P.width P.calibration true V {t} :=
  oneSlotWell _ _ _ _ _ _ _ (Set.mem_singleton _) (P.paint_support A t f R s h u) (P.paint_singlet A t f h)

end Purchases
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

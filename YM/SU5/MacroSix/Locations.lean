import YM.SU5.MacroSix.Lane
import YM.SU5.MacroSix.Receipt
/-! Prescribed geometry: any two axis-aligned open (nondegenerate) rectangles of centers
with strict separation margins between their compact closures. Also add optional price for
positioning *full field footprint* strictly inside the given rectangles (on a smaller
class of center supports). This isn't needed for the rank conclusion of `Macropositions`,
but another way to see the separation is not by hardcoded point labels. -/

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2200
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Aria Set

namespace Spine
open _root_.YM.MacroSix (SmoothDensity rectangle)

structure RectanglePose where
  lo : Vantage
  hi : Vantage
  strictWidth : ∀ i, lo i < hi i

namespace RectanglePose
variable (A B : RectanglePose) (signs : Axis → Bool)

def paints : Set Vantage := Set.pi univ fun i ↦ Set.Ioo (A.lo i) (A.hi i)
def charges : Set Vantage := Set.pi univ fun i ↦ Set.Icc (A.lo i) (A.hi i)
lemma paint_eq_box : A.paints = rectangle fun i ↦ Set.Ioo (A.lo i) (A.hi i) := by
  ext x; simp [paints,MacroSix.rectangle]
lemma charge_closed : closure A.paints=A.charges := by
  unfold paints charges; rw [closure_pi_set] -- name
  simp_rw [closure_Ioo (A.strictWidth _).ne]
lemma chargesCompact : IsCompact A.charges := isCompact_univ_pi fun i ↦ isCompact_Icc -- name
lemma paints_inside : A.paints ⊆ A.charges := A.charge_closed ▸ subset_closure
lemma open_paint : IsOpen A.paints := by rw [A.paint_eq_box]; exact MacroSix.rectangle_open _ fun _ ↦ isOpen_Ioo
lemma positive_paint : A.paints.Nonempty := by
  choose f a b using fun i ↦ exists_between (A.strictWidth i)
  exact ⟨f,fun i _ ↦ ⟨a i,b i⟩⟩

structure Across : Prop where
  forward : signs 3=true
  plus : ∀ i, signs i=true → A.hi i < B.lo i
  minus : ∀ i, signs i=false → B.hi i < A.lo i

/-- Can equally well start with unoriented disjoint transverse interval projections. -/
lemma selectSign (h : A.hi 3 < B.lo 3) (u : ∀ i : Axis, i ≠ 3 → A.hi i < B.lo i ∨ B.hi i < A.lo i) :
    ∃ signs, A.Across B signs := by
  let t(i : Axis) := decide (A.hi i < B.lo i)
  refine ⟨t,decide_eq_true h,fun i p ↦ of_decide_eq_true p, fun i p ↦ ?_⟩
  have hp : ¬ _ := of_decide_eq_false p
  by_cases v:i=3
  · subst i; exact (hp h).elim
  exact (u i v).resolve_left hp

structure Allows (P : Spine) (s n : ℕ) (A B : RectanglePose) (signs : Axis → Bool) : Prop where
  forward : signs 3=true
  plus : ∀ i, signs i=true → A.hi i + (P.sixWidth s n i:ℝ) < B.lo i - (P.sixWidth s n i:ℝ)
  minus : ∀ i, signs i=false → B.hi i + (P.sixWidth s n i:ℝ) < A.lo i - (P.sixWidth s n i:ℝ)

namespace Allows
variable {P : Spine} {s n : ℕ} {A B signs} (a : Allows P s n A B signs)
include a

lemma forwardOrder (y z : Vantage) (h : y∈ A.charges) (g : z∈B.charges) (j : Axis)
    (p : signs j=true) : P.fieldOrder s n j y z :=
  lt_of_le_of_lt (add_le_add_left (show y j ≤ A.hi j from (h j trivial).2) _)
    ((a.plus j p).trans_le (sub_le_sub_right (show B.lo j ≤ z j from (g j trivial).1) _))
lemma backwardOrder (y z : Vantage) (h : y∈ A.charges) (g : z∈B.charges) (j : Axis)
    (p : signs j=false) : P.fieldOrder s n j z y := by
  have he := (g j (Set.mem_univ j)).2; have hv := (h j (Set.mem_univ j)).1
  unfold fieldOrder; linarith [a.minus j p]

lemma fundedLane : A.charges ×ˢ B.charges ⊆ P.onLane s n signs := by
  rintro ⟨y,z⟩ ⟨y',z'⟩ i; change z i - y i ∈ P.laneSign s n i (signs i)
  cases p : signs i; exact (P.leftOf s n i y z).2 (a.backwardOrder y z y' z' i p); exact (P.rightOf s n i y z).2 (a.forwardOrder y z y' z' i p)

lemma timeFrame {f g : Vantage → ℝ} (p : tsupport f ⊆ A.charges) (q : tsupport g ⊆ B.charges) :
    P.OnFrame s n f g ((A.hi 3 + B.lo 3)/2) := by
  have he := a.plus 3 a.forward
  constructor
  · intro y t; have hv := (p t 3 (Set.mem_univ _)).2; linarith
  intro y t; have hv := (q t 3 (Set.mem_univ _)).1; linarith
end Allows

lemma allotted_late {P : Spine} {c r : ℕ → ℕ} (L : Prototype.Launch P c r) (h : A.Across B signs) :
    ∀ᶠ i in atTop, Allows P (c i) (r i) A B signs := by
  let w (n : ℕ) (i : Axis) : ℝ := P.sixWidth (c n) (r n) i
  have eh (j : Axis) : ∀ᶠ n in atTop, (signs j=true → A.hi j+w n j < B.lo j-w n j) ∧
      (signs j=false → B.hi j+w n j < A.lo j-w n j) := by
    cases hv : signs j <;> simp only [hv,Bool.false_eq_true,Bool.true_eq_false,false_implies,
      forall_true_left,and_true,true_and]
    · refine ((sixWidth_vanishes L j).eventually (gt_mem_nhds (show 0 < (A.lo j-B.hi j)/2 by linarith [h.minus j hv]))).mono fun i v ↦ ?_; unfold w; linarith
    refine ((sixWidth_vanishes L j).eventually (gt_mem_nhds (show 0 < (B.lo j-A.hi j)/2 by linarith [h.plus j hv]))).mono fun i v ↦ ?_; unfold w; linarith
  exact (Filter.eventually_all.mpr eh).mono fun i v ↦ ⟨h.forward,fun j ↦ (v j).1,fun j ↦ (v j).2⟩

def inset : RectanglePose :=
  ⟨fun i ↦ (2*A.lo i+A.hi i)/3, fun i ↦ (2*A.hi i+A.lo i)/3,
    fun i ↦ by linarith [A.strictWidth i]⟩
lemma insetLeft (i : Axis) : A.lo i < A.inset.lo i := by change _ < (2*_+_)/3; linarith [A.strictWidth i]
lemma insetRight (i : Axis) : A.inset.hi i < A.hi i := by change (2*_+_)/3 <_; linarith [A.strictWidth i]
lemma inset_subset : A.inset.charges⊆ A.paints := fun x p i t ↦
  ⟨lt_of_lt_of_le (A.insetLeft i) (p i t).1, lt_of_le_of_lt (p i t).2 (A.insetRight i)⟩

/-- Optional containment of the *whole* charged footprint inside the rectangle of interest;
here use the support budget in gauge doubled units (`Receipt`). -/
def Wraps (P : Spine) (s n : ℕ) (A : RectanglePose) :=
  (∀ (f : Vantage → ℝ), tsupport f ⊆ A.inset.charges → ∀ z : Window.Family,
    P.doubledBudget f (P.sixBody s n z) ⊆ {x | (1/2:ℝ) • x ∈ A.paints})

lemma snug_late {P : Spine} {c r : ℕ → ℕ} (L : Prototype.Launch P c r) :
    ∀ᶠ i in atTop, Wraps P (c i) (r i) A := by
  let w (n : ℕ) (i : Axis) : ℝ := P.sixWidth (c n) (r n) i
  have hp(i) : ∀ᶠ n in atTop, A.lo i+w n i < A.inset.lo i ∧
      A.inset.hi i < A.hi i-w n i := by
    filter_upwards [(sixWidth_vanishes L i).eventually (gt_mem_nhds (sub_pos.mpr (A.insetLeft i))),
      (sixWidth_vanishes L i).eventually (gt_mem_nhds (sub_pos.mpr (A.insetRight i)))] with i h p; unfold w; constructor <;> linarith -- index shadow
  filter_upwards [Filter.eventually_all.mpr hp] with n h f v z a p
  obtain ⟨y,w',s⟩ := p; intro i t; have z := v w' i t; obtain ⟨e,u⟩ := abs_le.mp (s i); obtain ⟨d,H⟩ := h i
  rw [P.sixBody_width] at e u; unfold w at *; change (A.lo i < (1/2:ℝ)*a i ∧ (1/2:ℝ)*a i < A.hi i)
  constructor <;> linarith [z.1,z.2]
end RectanglePose
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.RectanglePose
#print axioms snug_late
#print axioms Allows.fundedLane
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.RectanglePose

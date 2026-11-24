import YM.SU5.MacroSix.SeedPoint
import YM.SU5.MacroSix.Locations
import YM.SU5.MacroSix.Perturb

/-! # Part (ii) of `t:trans6`, including open density assertion for point-kernels.

Always uses `P.measureField`, so (by `P.measure_tends` at the stated frames) a limit of
the actual consultations. Pointwise continuity on ordered lanes, full price of bodies; and
local analytic extension of the matrix entries in each axis is on that axis, not a rotation
assumption on x. Gram version **not** asserted. Split comparison in separate module.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2200
set_option maxHeartbeats 340000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Aria Set
open _root_.YM.MacroSix

namespace Spine
variable (P : Spine) (s n : ℕ) (x : P.Spectrum0 3) (A B : RectanglePose)
    (signs : Axis → Bool)
local notation "K" => P.fieldKernel s n x
open RectanglePose

def live (W : Set (Vantage × Vantage)) := W ∩ {p | Success (P.fieldKernel s n x p.1 p.2)}

def HasLaneSeed := ∃ v : Vantage, v∈P.inLane s n signs ∧ Success (P.fieldKernel s n x 0 v)

structure Achieves (f g : Vantage → ℝ) : Prop where
  smoothLeft : SmoothDensity f
  smoothRight : SmoothDensity g
  paintsLeft : tsupport f ⊆ A.paints
  paintsRight : tsupport g ⊆ B.paints
  frame : P.OnFrame s n f g ((A.hi 3+B.lo 3)/2)
  succeeds : Success (P.measureField s n f g x)
  cost : ∀ (j k : Window.Family), Tendsto (fun t ↦ P.measureAt s n t f g x j k) atTop (𝓝 (P.measureField s n f g x j k))

variable (J : P.Ellis 3 x)
include J
lemma live_open {W : Set (Vantage×Vantage)} (h : IsOpen W)
    (p : ∀ (y z : Vantage), (y,z) ∈ W → P.fieldOrder s n 3 y z) : IsOpen (P.live s n x W) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨y,z⟩ ⟨v,d⟩
  have hp := h.mem_nhds v
  exact inter_mem hp (eventually_success _ (fun q : Vantage×Vantage ↦ K q.1 q.2) _
    (fun j k ↦ P.fieldKernel_cont s n j k x J (y,z) (p y z v)) d)

lemma live_dense {W : Set (Vantage×Vantage)} (h : IsOpen W) (v : W ⊆ P.onLane s n signs)
    (p : signs 3=true) (q : P.HasLaneSeed s n x signs) : W ⊆ closure (P.live s n x W) := by
  obtain ⟨y,hy,hY⟩ := q
  exact denseCost (fun i ↦ P.laneSign s n i (signs i)) (fun i ↦ P.laneSign_open s n i _)
    (fun i ↦ P.laneSign_connected s n i _) (F:= P.fieldKernel s n x) (P.fieldKernel s n x 0)
    (fun i y _ j k ↦ P.laneTest s n j k x i J (signs i) y) y hy hY W v
    (fun w u ↦ P.fieldKernel_move s n x J w.1 w.2 (P.sign_before s n 3 signs _ _ (v u) p)) h


lemma rectangle_result {signs : Axis → Bool}
    (h : RectanglePose.Allows P s n A B signs)
    (f g : Vantage → ℝ) (p : SmoothDensity f) (q : SmoothDensity g)
    (pf : tsupport f ⊆ A.paints) (pg : tsupport g ⊆ B.paints)
    (hf : Success (P.measureField s n f g x)) : P.Achieves s n x A B f g :=
  let frame := h.timeFrame (pf.trans A.paints_inside) (pg.trans B.paints_inside)
  ⟨p,q,pf,pg,frame,hf,fun i j ↦ P.measure_tends s n i j f g _ x p.smooth.continuous p.compact
    q.smooth.continuous q.compact J frame⟩

-- any open subposes (inside the fixed boxes). So can optimize for shape prices too.
lemma successes {C D : Set Vantage} (t : C⊆ A.paints) (v : D⊆ B.paints)
    (hp : IsOpen C) (hq : IsOpen D) (c : C.Nonempty) (d : D.Nonempty)
    (h : RectanglePose.Allows P s n A B signs) (u : P.HasLaneSeed s n x signs) :
    ∃ f g : Vantage → ℝ, P.Achieves s n x A B f g ∧ tsupport f⊆ C ∧ tsupport g⊆ D := by
  let W := C ×ˢ D
  have hf := t.trans A.paints_inside
  have hg := v.trans B.paints_inside
  have hw : W ⊆ P.onLane s n signs := Set.Subset.trans (Set.prod_mono hf hg) h.fundedLane
  have hd := P.live_dense s n x signs J (hp.prod hq) hw h.forward u
  obtain ⟨⟨a,b⟩,⟨P',Q'⟩,R⟩ := closure_nonempty_iff.mp ((c.prod d).mono hd)
  obtain ⟨f,g,p,f',q,g',w⟩ := reliable_pair (K) C D a b P' Q' hp hq R
    (fun i j ↦ P.fieldKernel_cont s n i j x J _ (h.forwardOrder a b (hf P') (hg Q') 3 h.forward))
    (fun f g p t q v i j ↦ (P.measureField_integral s n i j f g _ x p.smooth.continuous p.compact
      q.smooth.continuous q.compact J (h.timeFrame (t.trans hf) (v.trans hg))).1)
  exact ⟨f,g,P.rectangle_result s n x A B J h f g p q (f'.trans t) (g'.trans v) w, f',g'⟩

lemma variations {f g : Vantage → ℝ} (h : Allows P s n A B signs) (w : P.Achieves s n x A B f g)
    {a b : Vantage → ℝ} (pa : SmoothDensity a) (pb : SmoothDensity b)
    (p : tsupport a ⊆ A.paints) (q : tsupport b ⊆ B.paints) :
    ∀ᶠ r in 𝓝[>] (0:ℝ), P.Achieves s n x A B (rideLine a f r) (rideLine b g r) := by
  have he := successfulLines a f A.paints B.paints (K) b g
    (fun f g p pf q pg i j ↦ (P.measureField_integral s n i j f g _ x p.smooth.continuous p.compact
      q.smooth.continuous q.compact J (h.timeFrame (pf.trans A.paints_inside) (pg.trans B.paints_inside))).1)
    pa pb w.smoothLeft w.smoothRight p q w.paintsLeft w.paintsRight w.succeeds
  filter_upwards [he,self_mem_nhdsWithin] with i v t
  have hv : i ∈ Set.Icc (0:ℝ) 1 := ⟨(show 0 < i from t).le, v.1⟩
  exact P.rectangle_result s n x A B J h _ _ (ride_density a f pa w.smoothLeft i hv)
    (ride_density b g pb w.smoothRight i hv)
    ((ride_support ..).trans (Set.union_subset p w.paintsLeft))
    ((ride_support ..).trans (Set.union_subset q w.paintsRight)) v.2

omit J
/-- `Credited` packages the ordered pair results at fixed `s n`. Note the optional
wraps clause for keeping footprint actually in the given boxes on the inset version,
whereas the perturbation assertion in `Macropositions` is for density on the full
rectangles of centers, not preserving that extra inset. -/
structure Credited : Prop where
  margins : RectanglePose.Allows P s n A B signs
  wrapsLeft : RectanglePose.Wraps P s n A
  wrapsRight : RectanglePose.Wraps P s n B
  successful : ∃ f g, P.Achieves s n x A B f g ∧ tsupport f ⊆ A.inset.paints ∧ tsupport g ⊆ B.inset.paints
  nearby : ∀ (f g a b : Vantage → ℝ), P.Achieves s n x A B f g → SmoothDensity a → SmoothDensity b →
    tsupport a⊆ A.paints → tsupport b⊆ B.paints →
    ∀ᶠ r in 𝓝[>] (0:ℝ), P.Achieves s n x A B (rideLine a f r) (rideLine b g r)
  vivid : IsOpen (P.live s n x (A.paints ×ˢ B.paints))
  present : A.paints ×ˢ B.paints ⊆ closure (P.live s n x (A.paints ×ˢ B.paints))

include J
lemma toCredit (h : Allows P s n A B signs) (e : Wraps P s n A) (t : Wraps P s n B)
    (u : P.HasLaneSeed s n x signs) : P.Credited s n x A B signs :=
  ⟨h,e,t,P.successes s n x A B signs J (A.inset.paints_inside.trans A.inset_subset)
    (B.inset.paints_inside.trans B.inset_subset) A.inset.open_paint B.inset.open_paint
    A.inset.positive_paint B.inset.positive_paint h u,
    fun _ _ _ _ t p q a b ↦ P.variations s n x A B signs J h t p q a b,
    P.live_open s n x J (A.open_paint.prod B.open_paint)
      (fun i j e ↦ h.forwardOrder i j (A.paints_inside e.1) (B.paints_inside e.2) 3 h.forward),
    P.live_dense s n x signs J (A.open_paint.prod B.open_paint)
      ((Set.prod_mono A.paints_inside B.paints_inside).trans h.fundedLane) h.forward u⟩

variable {P x} {C r : ℕ → ℕ} (L : Prototype.Launch P C r)
    {d : ℕ → ℝ} (Y : Prototype.readyUV P C r x d) (p : Tendsto d atTop (𝓝 0))
    (q : P.lodestarHere 3 (P.otherSpectrum 3 3 x))
include L Y p q
/-- The theorem in independent open packets/rectangles (point-to-packet
technology only needs the grants indicated, on the same Spine). All parameters `x`, `C`,`r`
fixed here. Arbitrary prescribed distances (and signs) as long as strictly inside the
indicated conditions. -/
theorem lane_six (h : A.Across B signs) : ∀ᶠ i in atTop, P.Credited (C i) (r i) x A B signs := by
  filter_upwards [A.allotted_late B signs L h,A.snug_late L, B.snug_late L,
    laneSeed signs L Y p q J h.forward] with i m e f u
  exact toCredit P _ _ x A B signs J m e f ⟨P.smallLead signs (C i) (r i),u⟩

omit J L Y p q
lemma Credited.testClose {s n A B signs} (h : P.Credited s n x A B signs)
    (a b : Vantage → ℝ) (pa : SmoothDensity a) (pb : SmoothDensity b)
    (p : tsupport a⊆ A.paints) (q : tsupport b⊆ B.paints) (k : ℕ) (ε : ℝ) (e : 0<ε) :
    ∃ f g : Vantage → ℝ, P.Achieves s n x A B f g ∧
      ∀ j≤ k, ∀ x : Vantage, ‖iteratedFDeriv ℝ j (f - a) x‖ < ε ∧
        ‖iteratedFDeriv ℝ j (g - b) x‖ < ε := by
  obtain ⟨f,g,w,-⟩ := h.successful
  obtain ⟨r,i,y,z⟩ := ((h.nearby _ _ _ _ w pa pb p q).and (eventually_nhdsWithin_of_eventually_nhds
    ((ride_crests a f pa w.smoothLeft k ε e).and (ride_crests b g pb w.smoothRight k ε e)))).exists
  exact ⟨_,_,i,fun j h x ↦ ⟨y j h x,z j h x⟩⟩

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
#print axioms lane_six
#print axioms Credited.testClose
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

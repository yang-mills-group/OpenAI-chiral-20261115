import YM.SU5.MacroSix.Subscription
import YM.SU5.MacroSix.Purchase
import YM.SU5.MacroSix.AuditPocket

/-! # Assemble physical-location and spec for the requested READINGS

Ordered axis only (all-axis variant of ordering purchased too, below). Convergence of
these consultations `t → ∞` OUTERMOST. The deterministic limit input `D` is part of the
polynomial system at each of these heights. If using the *optional* extra finite-cost
implementation of the character value via PricePaid, demands period & cutoff cost FOR
those fixed heights and detector choices—same footprints are then honored even up to
each bare regulator. This agrees with the spatial & time spacing of the projected sector
version of the Euclidean fields, does not continue in the thickness of the body as
seeing finer t. One-point receipts are connected (=0 marginals); both tests independent
and real.
-/

set_option autoImplicit false
set_option maxHeartbeats 510000
set_option maxRecDepth 3400
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
  Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Reconstruction PhaseChoice Tapestry.Altitude
open Germ Alliance Lamour.Bridge.Celeste
open Designs Twah Prototype Altitude Aria Pockets
open _root_.YM.MacroSix
namespace Spine
variable (P : Spine) (R : P.Register) (s t n i : ℕ) (Z W : Window.Family) (f g : Vantage→ℝ)
    (α : P.Poll 3) (x : P.Spectrum0 3) (j : Axis) (A : P.Apron)
local notation "K"=> P.calibration
local notation "Y"=> P.run
local notation "Λ"=> P.par
local notation "B" z:max=> P.sixBody s n z
local notation "B'" z:max=> (P.sixBody s n z).kiss P 3
local notation "Γ"=> P.pose t
local notation "ρ"=> P.fieldKernel s n x
local notation "Φ" a:max=> P.nativeKernel s n a x
local notation "φ" a:max => P.singleState 3 a x
local notation "D" t:max z:max => P.smearField t f (B' z)
local notation "G" t:max z:max => P.smearField t g (B z)

-- `Metric` conversion to write some footprint constraints without products in statements.
def halvePose (p : Vantage) : RSpace:=fun j ↦ p j/2
private lemma halvePose_cont : Continuous halvePose:= continuous_pi fun x ↦ (continuous_apply x).div_const _
private lemma halve_self (p : RSpace) : halvePose (2 • p) = p := by funext i; simp [halvePose, two_smul]
private lemma double_self (p : RSpace) : 2 • halvePose p=p:=by funext i; simp [halvePose,two_smul]

def occupiedSpace : Set RSpace:= halvePose '' P.doubledBudget f A
local notation "A₀"=> P.occupiedSpace f A
lemma marks_area : handstamp (A₀)=P.doubledBudget f A := by
  ext u
  constructor
  · rintro ⟨v,p,h⟩; change halvePose v=halvePose u at h
    exact (by rw [← (show v=u from (double_self v).symm.trans
      ((congrArg (2 • ·) h).trans (double_self u)))]; exact p)
  intro p; exact ⟨u,p,rfl⟩

-- restate with the actual widths.
lemma positions_footprint : A₀={x : RSpace| ∃ v∈tsupport f, ∀ j:Axis,|x j-v j| ≤ A.realWidth P j}:=by
  ext x
  constructor
  · rintro ⟨v,⟨u,h,t⟩,rfl⟩; refine ⟨u,h,?_⟩; intro j
    obtain ⟨p,q⟩:= abs_le.mp (t j); unfold halvePose; rw [abs_le]; constructor <;> linarith
  rintro ⟨u,h,e⟩; refine ⟨(2:ℕ) • x,⟨u,h, fun i ↦ ?_⟩,halve_self x⟩
  rw [abs_le]; obtain ⟨p,q⟩:= abs_le.mp (e i); simp only [two_smul,Pi.add_apply]; constructor <;> linarith
local notation "D'" z:max => P.occupiedSpace f (B' z)
local notation "G'" z:max => P.occupiedSpace g (B z)

structure AddressPrice (c : ℝ) : Prop where
  funds : P.OnFrame s n f g c
  left (Z : Window.Family): IsCompact (P.occupiedSpace f ((P.sixBody s n Z).kiss P 3)) ∧
    P.occupiedSpace f ((P.sixBody s n Z).kiss P 3) ⊆ {x| x 3<c}
  right (Z : Window.Family): IsCompact (P.occupiedSpace g (P.sixBody s n Z)) ∧
    P.occupiedSpace g (P.sixBody s n Z)⊆ {x| c<x 3}

lemma OnFrame.coverPrice {P: Spine}{s n f g c} (p : P.OnFrame s n f g c) (h : HasCompactSupport f) (u : HasCompactSupport g) :
    P.AddressPrice s n f g c := by
  refine ⟨p,fun Z ↦ ⟨?_,?_⟩,fun W ↦ ⟨?_,?_⟩⟩
  · exact (P.doubledBudget_compact f _ h).image halvePose_cont
  · rintro x ⟨v,u,rfl⟩; have he : v 3 < 2*c := (p.places Z Z).1 u
    change v 3 / 2 < c; linarith
  · exact (P.doubledBudget_compact g _ u).image halvePose_cont
  rintro x ⟨v,u,rfl⟩; have he : 2*c < v 3 := (p.places W W).2 u
  change c < v 3/2; linarith

lemma AddressPrice.pe_gap {P: Spine} {s n f g c} (e : P.AddressPrice s n f g c) (Z W : Window.Family):
    Disjoint (P.occupiedSpace f ((P.sixBody s n Z).kiss P 3)) (P.occupiedSpace g (P.sixBody s n W)) :=
  Set.disjoint_left.mpr fun x a b ↦ not_le_of_gt (show x 3 < c from (e.left Z).2 a)
    (show c < x 3 from (e.right W).2 b).le

section rect
variable {L W₁ : RectanglePose} {p : Axis → Bool} (e : RectanglePose.Allows P s n L W₁ p)
include e
lemma mayPlace (h : tsupport f⊆ L.charges) (u : tsupport g⊆ W₁.charges) :
    ∀ x ∈ D' Z, ∀ y∈G' W, if p j then x j < y j else y j < x j := by
  intro x y v w
  rw [P.positions_footprint] at y w
  obtain ⟨U,h',c'⟩ := y; obtain ⟨V,u',d'⟩ := w
  obtain ⟨a,b⟩:= abs_le.mp (c' j); obtain ⟨c,d⟩:= abs_le.mp (d' j)
  rw [Apron.kiss_width,P.sixBody_width] at a b; rw [P.sixBody_width] at c d
  split
  · rename_i k; have he:= e.forwardOrder U V (h h') (u u') j k; unfold fieldOrder at he; linarith
  rename_i k; have he:= e.backwardOrder U V (h h') (u u') j (Bool.eq_false_iff.mpr k); unfold fieldOrder at he; linarith
omit e
lemma RectanglePose.snugLocations (e : RectanglePose.Wraps P s n L)
    (p : tsupport f ⊆ L.inset.charges) : D' Z ⊆ L.paints ∧
      P.occupiedSpace f (B Z) ⊆ L.paints := by
  have h : P.occupiedSpace f (B Z) ⊆ L.paints:= fun x t ↦ by
    obtain ⟨u,d,rfl⟩:= t
    have h : halvePose u=(1/2:ℝ) • u:=by funext i; simp [halvePose]; ring
    rw [h]; exact e f p Z d
  exact ⟨h,h⟩
end rect

lemma meshCharge : P.meshSize t=(ruler P.par.block:ℤ)*Selected.gaugeMesh P.par t := by
  let h:=P.meshSize t
  have he:= Selected.double_clock_calibration Λ t 1
  simpa [meshSize,h,whenly] using he

include R in
lemma compassPol (h : HasCompactSupport f)(u : A.s≤ t) :
    P.smearField t f A∈ keep Λ P.width t K true (handstamp A₀) ∧
    P.smearField t f A ∈ enclave K ∧
    pinhole P.Test t (P.smearField t f A)∈ PolAt Y P.large t A₀ := by
  rw [P.marks_area]; obtain ⟨q,a⟩:= P.smear_locates t f A R u h
  refine ⟨q,a, oneSlotWell Λ K P.width true _ _ _ (by simp) ?_ a⟩
  rw [P.marks_area]; exact q

lemma scrolling (a b : Finset Cover) (p : Function.support (f ∘ P.pose t) ⊆ a)
    (u : Function.support (g ∘ P.pose t) ⊆ b) : P.measureAt s n t f g x Z W =
    (↑((P.meshSize t)^4):ℂ)^2 *∑ i∈ a, ∑ j ∈ b, (f (P.pose t i):ℂ) * (g (P.pose t j):ℂ) * P.nativeKernel s n t x i j Z W :=
  finiteTest_product (f ∘ Γ) (g ∘ Γ) _ (P.fieldAt t (B' Z)) (P.fieldAt t (B W)) (φ t) a b p u

/-- Each fine consultation, PROPER labels on the elected signed values.
If pricing these extra regulator facts fix `t` before placing period & cutoff queries.
(Embellishment via higher polynomials just in case: confirms normalization and physical
support can still be paid using available actual sensors.) -/
structure Consult : Prop where
  age : s≤t
  marks (Z : Window.Family) : D t Z∈enclave K ∧ G t Z∈enclave K ∧
    pinhole P.Test t (D t Z)∈ PolAt Y P.large t (D' Z) ∧
    pinhole P.Test t (G t Z)∈ PolAt Y P.large t (G' Z)
  centers (Z : Window.Family) : (φ t) (D t Z)=0 ∧ (φ t) (G t Z)=0
  seen(z w : Window.Family): P.measureAt s n t f g x z w=P.spirits R 3 x
    (pinhole P.Test t (D t z) * pinhole P.Test t (G t w))
  receives (c : P.Poll 3) (C : P.Selects R 3 x c) (z w : Window.Family) :
    P.PricePaid R 3 c t x (D' z) (G' w) (pinhole P.Test t (D t z)) (pinhole P.Test t (G t w))
  frame : ∃ c : ℝ,P.AddressPrice s n f g c
  opponent : ∀ F : P.Test →ₗ[ℂ] ℂ, PaintedSplit P.par t F → P.respond s t n f g F=0
  direct : P.measureAt s n t f g x=P.respond s t n f g (P.singleState 3 t x)

lemma obeys_consult (h : HasCompactSupport f) (u : HasCompactSupport g)
    {c : ℝ}(w : P.OnFrame s n f g c)(p : P.StockClear n)(e : s ≤ t) :
    P.Consult R s t n f g x := by
  have hv:=OnFrame.coverPrice w h u
  have he Z := P.compassPol R t f (B' Z) h e
  have hw Z := P.compassPol R t g (B Z) u e
  refine ⟨e,fun z ↦ ⟨(he z).2.1,(hw z).2.1,(he z).2.2,(hw z).2.2⟩,fun z ↦ P.measureAt_centered s n t z z f g x e h u,
    ?_,?_,⟨c,hv⟩,fun G₁ p' ↦ P.frameZero s t n R p' f g p e h u w,(P.trueResponse ..).symm⟩
  · intro z i
    rw [← map_mul]; exact (P.oneCup ..).symm
  intro a k z i
  exact Selects.pairsCost P R _ a _ x _ _ k (he z).2.2 (hw i).2.2 (hv.left z).1 (hv.right i).1 (hv.pe_gap z i)

lemma consult_limit (J : P.Ellis 3 x) (q : SmoothDensity f) (h : SmoothDensity g)
    {c:ℝ} (w : P.OnFrame s n f g c) :
    (Integrable (weightKernel (fun y z ↦ P.fieldKernel s n x y z Z W) f g)) ∧
    Tendsto (fun t ↦ P.measureAt s n t f g x Z W) atTop (𝓝 (P.measureField s n f g x Z W)) :=
  ⟨(P.measureField_integral s n Z W f g c x q.smooth.continuous q.compact h.smooth.continuous
    h.compact J w).1, P.measure_tends s n Z W f g c x q.smooth.continuous q.compact h.smooth.continuous
    h.compact J w⟩

/-- Extra verification: the point-kernel assertion in rectangles, too, refers to the physical
paid readings and doesn't require an invented continuous version of unprojected translations on H'. -/
structure PlacedPoints (A B₁ : RectanglePose) : Prop where
  exact_grid : ∀ t, s≤t→ ∀ (u v : Cover), P.pose t u∈ A.charges → P.pose t v∈ B₁.charges →
    P.nativeKernel s n t x u v = P.fieldKernel s n x (P.pose t u) (P.pose t v)
  movement : ∀ y ∈ A.charges, ∀ z∈ B₁.charges, ∀ a b : ℕ → Cover,
    Tendsto (fun i ↦ P.pose i (a i)) atTop (𝓝 y) → Tendsto (fun i ↦ P.pose i (b i)) atTop (𝓝 z) →
    ∀ i j:Window.Family,Tendsto (fun t ↦ P.nativeKernel s n t x (a t) (b t) i j) atTop (𝓝 (P.fieldKernel s n x y z i j))
  location : ∀ f g : Vantage → ℝ, tsupport f ⊆ A.charges → tsupport g ⊆ B₁.charges →
    ∀ i j : Window.Family, ∀ a:Axis, Disjoint ((fun v:RSpace↦ v a) '' P.occupiedSpace f ((P.sixBody s n i).kiss P 3))
      ((fun v:RSpace↦ v a) '' P.occupiedSpace g (P.sixBody s n j))

lemma PlacedPoints.places (L W₁ : RectanglePose) (u : Axis→ Bool) (e : RectanglePose.Allows P s n L W₁ u)
    (J : P.Ellis 3 x) : P.PlacedPoints s n x L W₁ := by
  have ht := e.fundedLane
  have hp(r:ℕ)(h:s≤r) (p q:Cover)(v : (P.pose r p,P.pose r q)∈ P.onLane s n u) (z w) :
      (Φ r) p q z w = ρ (P.pose r p) (P.pose r q) z w:= (P.fieldKernel_plenum s n r z w x J h p q
        (P.sign_before s n 3 u (P.pose r p) _ v e.forward) (P.plenum_onLane s n z w u _ _ v)).symm
  refine ⟨fun t h p q z w ↦ ?_,fun y z x₀ b a d p q i j ↦ ?_, fun a b x y i j v ↦ ?_⟩ -- `exact_grid` ext
  · exact Matrix.ext fun i j ↦ hp t h p q (ht ⟨z,w⟩) i j
  · let T (i:ℕ):= (P.pose i (a i), P.pose i (d i))
    have he := ht (show (y,x₀)∈ _ from ⟨z,b⟩)
    have h : Tendsto T atTop (𝓝 (y,x₀)):= p.prodMk_nhds q
    exact ((P.fieldKernel_cont s n i j x J (y,x₀) (P.sign_before s n 3 u y x₀ he e.forward)).tendsto.comp h).congr'
      (((eventually_ge_atTop s).and (h.eventually ((P.onLane_open s n u).mem_nhds he))).mono
        fun t ⟨i',p'⟩ ↦ (hp t i' (a t) (d t) p' i j).symm)
  -- note shadow `x`
  apply Set.disjoint_left.mpr
  rintro k ⟨p,v',rfl⟩ ⟨t,p',eq : t v= p v⟩
  have he:= P.mayPlace s n i j a b v e x y p v' t p'
  split at he <;> linarith only [eq,he]

lemma poses_approach (a : Vantage) : ∃ u : ℕ → Cover,
    Tendsto (fun i ↦ P.pose i (u i)) atTop (𝓝 a) := by
  let u : ℕ → Cover := fun i ↦ MacroSix.Grid.tag (P.meshSize i) a
  refine ⟨u,Metric.tendsto_nhds.mpr (fun ε h ↦ ?_)⟩
  filter_upwards [(NNReal.tendsto_coe.mpr (vanishes (timeMesh Λ))).eventually (gt_mem_nhds h)] with i ht
  exact (dist_comm ..).trans_lt ((MacroSix.Grid.distance_tag _ (P.meshSize_pos i) a).trans_lt ht)

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
#print axioms occupiedSpace
#print axioms positions_footprint
#print axioms mayPlace
#print axioms obeys_consult
#print axioms consult_limit
#print axioms PlacedPoints.places
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

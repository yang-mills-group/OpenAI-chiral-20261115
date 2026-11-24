import VerifiedSatinGroundInteraction

/-!
# Fixed physical texture: first milestone (before extremal selection)

Freeze the *observing* level, not the cutoff; from then on use the very same test including for
all refinements via the Coherent history. A single Filigree observable is enough to work with on
all four axes. Separation in this file means the following: in the initiating stencil EVERY
creation endpoint of EACH allowed `CRow.pair` is at positive physical distance from ALL its
allowed anchor sites (including its paired removal endpoint); `Filigree` already imposes that at
level s in cover coordinates. State a uniform bound for it in true real coordinates (gauge units
of level 0, `addressG`, with offsets). This is not disjointness of gauge and matter supports!
The gauge coefficient can run right up to these endpoints. Nor asserting that the individual
letters are separately refined and still at disjoint supports at all resolutions. Need
`Detached`-sized gaps and suitable marks for the verified product refinement laws; letters
separated by 1 fermion mesh step needn't give that. We treat the whole mixed insertion as one
local observable and track its reading and physical shield. Separate claims about multiple
insertions and the nature of the footprint must be proved in addition.
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
open Tapestry Vacancy CF.Pannier.Chancel Papal

/-- Coordinates of the physical charged-letter endpoint in units of level-zero gauge spacing. -/
abbrev endpointAt (Λ : Preparation) (s : ℕ) (x : Cover) : RSpace :=
  addressG Λ s (nodeC x)

/-- RSpace uses the sup metric. Two gauge lattice steps (at the observing level),
with scale and offset retained. -/
theorem endpoints_far (Λ : Preparation) (s : ℕ) {x y : Cover} (h : x ≠ y) :
    2 / precisionAt Λ s ≤ dist (endpointAt Λ s x) (endpointAt Λ s y) := by
  have he : ∃ j : Axis, x j ≠ y j := by
    by_contra! k
    exact h (funext k)
  obtain ⟨j, H⟩ := he
  apply le_trans _ (dist_le_pi_dist (endpointAt Λ s x) (endpointAt Λ s y) j)
  have ht : 0 < precisionAt Λ s := positiveScale ..
  change _ ≤ dist (markZ Λ s (nodeC x j)) (markZ Λ s (nodeC y j))
  rw [nodePrint, nodePrint, Real.dist_eq, ← sub_div, abs_div, abs_of_pos ht]
  apply div_le_div_of_nonneg_right _ ht.le
  rcases lt_or_gt_of_ne H with p|p
  · have hv : (x j : ℝ) + 1 ≤ y j := by exact_mod_cast p -- successor?
    linarith [neg_le_abs ((2 * (x j : ℝ) + 1) - (2 * (y j : ℝ) + 1))]
  · have hv : (y j : ℝ) + 1 ≤ x j := by exact_mod_cast p
    linarith [le_abs_self ((2 * (x j : ℝ) + 1) - (2 * (y j : ℝ) + 1))]

theorem transport_location (Λ : Preparation) (l s n : ℕ) (X : Finset Cover)
    (O : Set RSpace) (p : printedHere Λ l s X O) :
    printedHere Λ l (s+n) (volumeAround Λ l n X) O := by
  induction n with
  | zero => exact p
  | succ n ih => exact shielding Λ l (s+n) O _ ih

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))

structure PhysicalTexture {m : ℕ} (F : Family (tent Y H)) (z : SU.Slot)
    (s : ℕ) (X : Finset Cover) (u : Fin m → Cover) (O : Set RSpace)
    (δ : ℝ) : Prop where
  inject : Injective u
  arrives (j : Fin m) : nodeC (u j) ∈ X
  gap_pos : 0 < δ
  separation (y : Cover) (h : ∀ j, y ≠ u j) (j : Fin m) :
    δ ≤ dist (endpointAt Λ s y) (endpointAt Λ s (u j))
  gauge : Tapestry.Neutral K F
  initiates : F ∈ Filigree K (Window.family z) u X
  confined : printedHere Λ l s X O

variable {m : ℕ} {X : Finset Cover} {δ : ℝ} {z : SU.Slot} {s n : ℕ} {F : Family (tent Y H)}
  {u : Fin m → Cover} {O : Set RSpace} (h : PhysicalTexture Y H F z s X u O δ)

/-- Available also in the full even (gauge-covariant extension) workspace. -/
def PhysicalTexture.enter (r : Bool) : Vacancy.observable K r :=
  ⟨F, Tower.aux_test ((FilTest h.initiates).widen), fun _ => h.gauge⟩

include Q h in
theorem PhysicalTexture.refines :
    let Xn := volumeAround Λ l n X
    let G := stream Y H D s n F
    G ∈ observ K Xn true ∧ printedHere Λ l (s+n) Xn O ∧ E (s+n) G = E s F :=
  ⟨Tower.chroma Y H Q.circuit s n ((obs_in ..).mpr ⟨(FilTest h.initiates).widen, h.gauge⟩),
   transport_location Λ l s n X O h.confined,
   (proceeds Y H Q.circuit s n (FilTest h.initiates).widen).2⟩

include Qc V Q
/-- Can take the same test as the input to the ground read on every axis. Exact operator
(up to identity in the same joint ground space) at all refinements. -/
theorem PhysicalTexture.inGround (j : Axis) (r : Bool) (C : Arena Y H Q.circuit j 0 r) :
    let f := h.enter Y H r
    let g := cap Y H V s Q Qc j r C f
    let v := seat0 Y H V Q j r C
    inner ℂ v (g v) = E s F ∧
    ∀ n : ℕ, cap Y H V (s+n) Q Qc j r C (upward Y H Q r f s n) = g := by
  dsimp only
  refine ⟨inspected Y H V s Q Qc j r C (F := h.enter Y H r), fun n => ?_⟩
  simpa only [Nat.add_sub_cancel_left] using
    cap_level Y H V s Q Qc j r C (F := h.enter Y H r) (s+n) (by omega)

omit Q Qc
/-- Support and level are selected ONCE. Magnitude lower bound not weakened at all on
refining (use `inGround` and `refines`). `N` may be picked arbitrarily far up the
observing ladder. Different z may pick different probes. -/
theorem choose_fixed {q d w : ℕ} {C Z : ℝ} (g : Cornet Y H q d w C Z)
    (N : ℕ) (z : SU.Slot) (x : Cover) :
    let X := Sen x (payout d q w)
    ∃ (s R : ℕ) (F : Family K), N ≤ s ∧
      PhysicalTexture Y H F z s X (booty x d q) (cabin R) (2 / precisionAt Λ s) ∧
      1 / 4 ≤ ‖E s F‖ := by
  intro X
  obtain ⟨s, p, u⟩ := ((certificate Y H C Z z g I E V).and (eventually_ge_atTop N)).exists
  obtain ⟨_, _, F, _, k, h, _, _, hx⟩ := p x
  obtain ⟨R,v⟩ := (fundCabin Λ l s X).exists
  have h0 := positiveScale Λ s
  refine ⟨s,R,F,u,⟨g.cents x, stake_centers Y H x d q w, ?_, ?_, h,k,v⟩,hx⟩
  · positivity
  exact fun y e j => endpoints_far Λ s (e j)

end YM.CF.Buffered.Afterglow.Tower.Selection

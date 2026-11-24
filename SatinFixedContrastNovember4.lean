import SatinSixCompatibility
import YM.SU5.Six.Trans6

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 28000
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
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six

/-- The complete finite stencil, including its footprint and clock, is the earlier Satin stencil. -/
theorem reviewWardBody (P : Spine) (Z : Lead.Clan) (s n : ℕ) :
    P.experimentBody Z s n = P.macroBody Z s n := by rfl

/-- Both quadratures sample the same compact support on exactly the same physical grid. -/
theorem reviewWardSites (P : Spine) (t : ℕ) (F : SampleDose) :
    P.usedGrid t F = P.fineSites t F.budget :=
  Finset.ext fun q => (P.usedPose t F q).trans (P.fine_mem t F.budget q).symm

theorem reviewWardPaint (P : Spine) (t : ℕ) (A : P.Apron) (F : SampleDose) :
    P.prepared t A F = P.paintMark A t F.val := by
  rw [P.prepared_literal, paintMark, P.fine_sum t F.budget, P.reviewWardSites]
  push_cast
  rfl

/-- Equality of the actual normalized reading on each refinement, for this character and these tests. -/
theorem reviewWardRaw (P : Spine) (K : P.Register) (x : P.Spectrum0 3)
    (s n t : ℕ) (F G : SampleDose) (Z W : Lead.Clan) :
    P.arrayFine x s n t F G Z W = P.spirits K 3 x
      (P.paintPair ((P.macroBody Z s n).kiss P 3) (P.macroBody W s n) t F.val G.val) := by
  rw [P.pin_paintPair]
  simpa only [RTest, FTest, reviewWardBody, reviewWardPaint, markPair] using
    (P.fineReading x s n K t F G Z W).2

def FixedSatinReadings (P : Spine) (K : P.Register) (x : P.Spectrum0 3)
    (s n : ℕ) (a : ℝ) (F G : SampleDose) : Prop :=
    ReadsSix (P.arrayReading x s n a F G) ∧
    Tendsto (fun t : ℕ => Matrix.of fun Z W : Lead.Clan => P.spirits K 3 x
      (P.paintPair ((P.macroBody Z s n).kiss P 3) (P.macroBody W s n) t F.val G.val))
      atTop (𝓝 (P.arrayReading x s n a F G)) ∧
    ∀ (t : ℕ), s ≤ t → ∀ (X : P.Test →ₗ[ℂ] ℂ), Factors P.calibration X →
      MatterWard P.calibration X ∨ GaugeWard P.calibration X → ∀ Z W : Lead.Clan,
      X (P.markPair ((P.macroBody Z s n).kiss P 3) (P.macroBody W s n) t F.val G.val) = 0

/-- The earlier actual joint price converges on this single vacuum. Every Ward-factorized
    raw price vanishes on the same fixed marks at every eligible refinement. -/
theorem reviewWardContrast (P : Spine) (K : P.Register) (x : P.Spectrum0 3)
    (s n : ℕ) (a : ℝ) (F G : SampleDose) (R : P.ReturnsSix x s n a F G) :
    P.FixedSatinReadings K x s n a F G := by
  refine ⟨R.poles, R.steady.congr (fun t => ?_), ?_⟩
  · ext1 Z W
    exact P.reviewWardRaw K x s n t F G Z W
  · intro t ht X hF hW Z W
    have h := congrArg (fun T : CrossRead => T Z W) (R.disqualifies t ht X hF hW)
    simpa only [splitArray, Matrix.of_apply, Matrix.zero_apply, RTest, FTest, reviewWardBody,
      reviewWardPaint, markPair] using h

/-- One character is chosen before all rectangles and six families. For each late fixed
    physical stencil the same two smooth tests work on every eligible refinement. -/
theorem reviewElectedFixedContrast (Y : Supplier) (L M : ℝ) (hM : 0 < M) (z : ℕ → ℕ) :
    ∃ (P : Spine) (K : P.Register), uniform P K Y L M ∧
      ∃ (c r : ℕ → ℕ) (x : P.Spectrum0 3), z ≤ r ∧
        ∀ (U V : Doorway) (order : Orders), U.Later V order 0 → ∀ᶠ i : ℕ in atTop,
          ∃ (a : ℝ) (F G : SampleDose), F.Normalized ∧ G.Normalized ∧
            tsupport F.val ⊆ U.invites ∧ tsupport G.val ⊆ V.invites ∧
            P.ReturnsSix x (c i) (r i) a F G ∧ P.FixedSatinReadings K x (c i) (r i) a F G := by
  obtain ⟨P, K, h, c, r, x, hz, _J, _experiment, T⟩ := macroscopicSatin Y L M hM z
  refine ⟨P, K, h, c, r, x, hz, ?_⟩
  intro U V order sep
  let b : Fin 3 → Bool := fun _ => false
  obtain ⟨p, e, _he, _inside, hcost⟩ := authorize b
  filter_upwards [packs_within_rectangles T (Metric.ball p e) b hcost U V order sep] with i hi
  obtain ⟨a, F, G, hF, hG, hR, hU, hV, _⟩ := hi.2
  exact ⟨a, F, G, hF, hG, hU, hV, hR, P.reviewWardContrast K x _ _ a F G hR⟩

/-- The supplier in the general theorem is a real-valued request function. A constant
    request exhibits a physical course and elected vacuum without an existence assumption. -/
theorem reviewConcreteFixedContrast :
    ∃ (P : Spine) (K : P.Register) (c r : ℕ → ℕ) (x : P.Spectrum0 3),
      (∀ i, i ≤ r i) ∧ ∀ (U V : Doorway) (order : Orders), U.Later V order 0 →
        ∀ᶠ i : ℕ in atTop, ∃ (a : ℝ) (F G : SampleDose), F.Normalized ∧ G.Normalized ∧
          tsupport F.val ⊆ U.invites ∧ tsupport G.val ⊆ V.invites ∧
          P.ReturnsSix x (c i) (r i) a F G ∧ P.FixedSatinReadings K x (c i) (r i) a F G := by
  let request : Supplier := fun _ _ _ _ _ _ _ _ _ _ _ _ => 0
  obtain ⟨P, K, _uniform, c, r, x, hr, h⟩ :=
    reviewElectedFixedContrast request 1 1 (by norm_num) id
  exact ⟨P, K, c, r, x, hr, h⟩

def reviewEarlierBox : Doorway := ⟨fun _ => -2, fun _ => -1, fun _ => by norm_num⟩
def reviewLaterBox : Doorway := ⟨fun _ => 1, fun _ => 2, fun _ => by norm_num⟩

/-- An unconditional example with fixed, strictly separated physical boxes. -/
theorem reviewTwoFixedProbes :
    ∃ (P : Spine) (K : P.Register) (x : P.Spectrum0 3) (s n : ℕ) (a : ℝ) (F G : SampleDose),
      F.Normalized ∧ G.Normalized ∧ tsupport F.val ⊆ reviewEarlierBox.invites ∧
        tsupport G.val ⊆ reviewLaterBox.invites ∧
        P.ReturnsSix x s n a F G ∧ P.FixedSatinReadings K x s n a F G := by
  obtain ⟨P, K, c, r, x, _hr, h⟩ := reviewConcreteFixedContrast
  let order : Orders := ⟨fun _ => true, rfl⟩
  have sep : reviewEarlierBox.Later reviewLaterBox order 0 := by
    intro j
    norm_num [Doorway.Later, reviewEarlierBox, reviewLaterBox, order]
  obtain ⟨i, a, F, G, hF, hG, hU, hV, hR, hC⟩ := (h _ _ order sep).exists
  exact ⟨P, K, x, c i, r i, a, F, G, hF, hG, hU, hV, hR, hC⟩

#print axioms reviewTwoFixedProbes
#print axioms reviewConcreteFixedContrast
#print axioms reviewElectedFixedContrast
#print axioms reviewWardBody
#print axioms reviewWardSites
#print axioms reviewWardPaint
#print axioms reviewWardRaw
#print axioms reviewWardContrast
#print axioms packs_within_rectangles
#print axioms macroscopicSatin
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

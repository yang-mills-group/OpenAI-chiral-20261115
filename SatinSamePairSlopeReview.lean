import SatinConnectedSmearsReview
import Thin.T0
import ThinSlopePlateau
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

/-- On one Satin election, the same two fixed smears give the original fixed-width
contrast, the nonzero undifferenced thin front, and the quantitative loss of the
original time difference even after each insertion is divided by its increment. -/
theorem reviewSamePairRawAndSlope :
    ∃ (P : Spine) (K : P.Register) (c r : ℕ → ℕ) (x : P.Spectrum0 3)
      (i : ℕ) (a : ℝ) (F G : SampleDose),
      F.Normalized ∧ G.Normalized ∧ tsupport F.val ⊆ reviewEarlierBox.invites ∧
      tsupport G.val ⊆ reviewLaterBox.invites ∧ P.ReturnsSix x (c i) (r i) a F G ∧
      P.FixedSatinReadings K x (c i) (r i) a F G ∧
      (∀ ε > 0, ∀ᶠ j : ℕ in atTop, ∀ Z : Lead.Clan,
        P.ThinIntrinsic (P.thinString Z (c j) (r j)) ε ∧
        P.ThinIntrinsic ((P.thinString Z (c j) (r j)).kiss P 3) ε) ∧
      P.ThinFrontReadings x c r F G ∧
      (∀ Z W : Lead.Clan, Tendsto (fun j : ℕ =>
        ‖P.arrayReading x (c j) (r j) 0 F G Z W‖ / (P.increment (c j) (r j) : ℝ)^2)
        atTop (𝓝 0)) ∧
      Tendsto (fun j : ℕ => P.slopeReading x (c j) (r j) 0 F G) atTop (𝓝 (0 : CrossRead)) := by
  let request : Supplier := fun _ _ _ _ _ _ _ _ _ _ _ _ => 0
  obtain ⟨P, K, _uniform, c, r, x, hr, _J, B, T⟩ := macroscopicSatin request 1 1 (by norm_num) id
  let order : Orders := ⟨fun _ => true, rfl⟩
  have sep : reviewEarlierBox.Later reviewLaterBox order 0 := by
    intro j
    norm_num [Doorway.Later, reviewEarlierBox, reviewLaterBox, order]
  let b : Fin 3 → Bool := fun _ => false
  obtain ⟨p, e, _he, _inside, cost⟩ := authorize b
  obtain ⟨i, hi⟩ :=
    (packs_within_rectangles T (Metric.ball p e) b cost reviewEarlierBox reviewLaterBox order sep).exists
  obtain ⟨a, F, G, hF, hG, hR, hU, hV, _⟩ := hi.2
  have neg : thinNegative F 1 := by
    intro z hz
    exact ((hU hz) 3 (Set.mem_univ _)).2.le
  have pos : thinPositive G 1 := by
    intro z hz
    exact ((hV hz) 3 (Set.mem_univ _)).1.le
  have early : ∀ _i : ℕ, ∀ v ∈ tsupport F.val, (1 : ℝ) ≤ (0 : ℝ) - v (3 : Axis) := by
    intro i v hv
    have h := neg v hv
    norm_num at h
    linarith only [h]
  have late : ∀ _i : ℕ, ∀ v ∈ tsupport G.val, (1 : ℝ) ≤ v (3 : Axis) - (0 : ℝ) := by
    intro i v hv
    have h := pos v hv
    norm_num at h
    linarith only [h]
  refine ⟨P, K, c, r, x, i, a, F, G, hF, hG, hU, hV, hR,
    P.reviewWardContrast K x _ _ a F G hR, thin_widths T,
    reviewThinSmears B T hr F G hF hG neg pos, ?_, plateauSlope B F G hU hV hF hG⟩
  intro Z W
  exact Thin.joint_o B Z W 0 1 (by norm_num) (fun _ => F) (fun _ => G)
    (fun _ => hF) (fun _ => hG) early late

#print axioms reviewSamePairRawAndSlope
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

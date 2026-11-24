import SatinSamePairSlopeReview
import YM.SU5.Thin.Closing
import YM.SU5.ThinInteraction.Detect

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

/-- The operator limit, the raw product test, the loss of the original time
difference, and the finite-width carrier supply use one character and one
trajectory. The first three readings use exactly the same two test functions. -/
theorem reviewOperatorsOnOneElection :
    ∃ (P : Spine) (K : P.Register) (c r : ℕ → ℕ) (x : P.Spectrum0 3)
      (i : ℕ) (a : ℝ) (F G : SampleDose) (b : ℕ → ℕ)
      (D : ∀ Z : Lead.Clan, P.VoucherOp x Z (r i) b),
      P.GetsThin K x c r i a F G b D ∧
      P.FixedSatinReadings K x (c i) (r i) a F G ∧
      P.ThinFrontReadings x c r F G ∧
      (∀ Z W : Lead.Clan, Tendsto (fun j : ℕ =>
        ‖P.arrayReading x (c j) (r j) 0 F G Z W‖ / (P.increment (c j) (r j) : ℝ)^2)
        atTop (𝓝 0)) ∧
      Tendsto (fun j : ℕ => P.slopeReading x (c j) (r j) 0 F G) atTop (𝓝 (0 : CrossRead)) ∧
      (∀ cost : Lead.Clan → ℝ, (∀ Z, 0 < cost Z) → ∀ᶠ j : ℕ in atTop,
        ∀ Z, Nonempty (Thinning.Portfolio x (c j) (r j) (cost Z) Z)) := by
  obtain ⟨P, K, r, x, J, c, _budget, hr, _repeater, B, i, a, F, G, b, D, _static, paid⟩ :=
    satinTwoThinFields
  obtain ⟨hF, hG, hU, hV⟩ := paid.oldData
  have T : P.Transmission x c r := trans6 B
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
  refine ⟨P, K, c, r, x, i, a, F, G, b, D, paid, paid.retest.2,
    reviewThinSmears B T hr F G hF hG neg pos, ?_, plateauSlope B F G hU hV hF hG, ?_⟩
  · intro Z W
    exact Thin.joint_o B Z W 0 1 (by norm_num) (fun _ => F) (fun _ => G)
      (fun _ => hF) (fun _ => hG) early late
  · intro cost positive
    filter_upwards [Thinning.cofinance K c r J B T cost positive] with j hj
    intro Z
    obtain ⟨portfolio, _⟩ := hj Z
    exact ⟨portfolio⟩

#print axioms reviewOperatorsOnOneElection
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

import YM.SU5.LoomForce.Placement
import YM.SU5.Satin.BookedStaffOnOnePreparation

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
universe u

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP
     Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Papal Lamour.Bridge Celeste Exterior SpinReceipt Yoke Jewel EmberWind Hiro Onyx
open Regis.Head Regis.Head.Brecht Regis.Circuit
open YM.Stationary (Gaia)
open scoped Topology Classical
open LoomForce

/-- The explicit adjacent staff on the retained mesh layout at a given point. -/
def positionedStaff (P : Spine) (A : ℝ) (x : Gaia) (F : PlaqAxes) (L : Twah.DirSpin) :
    ℕ → Staff :=
  fun s => adjacent (advice P A 1 0 x s) F L

def positionedWeave (P : Spine) (A : ℝ) (x : Gaia) (F : PlaqAxes) (L : Twah.DirSpin)
    (r : ℕ) (β : ℕ → ℝ) (s : ℕ) : Papal.Weaver :=
  weaving P A (positionedStaff P A x F L s) r s β

def positionedTest (P : Spine) (A : ℝ) (x : Gaia) (F : PlaqAxes) (L : Twah.DirSpin)
    (r : ℕ) (β : ℕ → ℝ) : ℕ → P.Test :=
  bookedStaffTest P A (positionedStaff P A x F L) (fun _ => r) β

/-- The actual averaged covariance at any two distinct prescribed rescaled
positions. The mesh positions and the funding for this staff pair are explicit. -/
def PositionedStaffCovariance (P : Spine) (β : ℕ → ℝ) : Prop :=
  ∀ (A : ℝ), 0 < A → ∀ (x y : Gaia), x ≠ y →
    ∀ (F D : PlaqAxes) (L G : Twah.DirSpin) (r : ℕ), 4 ≤ r →
    let first := positionedWeave P A x F L r β
    let second := positionedWeave P A y D G r β
    Tendsto (fun s => infiniteE P s (first s)) atTop (𝓝 0) ∧
    Tendsto (fun s => infiniteE P s (second s)) atTop (𝓝 0) ∧
    Tendsto (fun s => infiniteE P s (first s * second s) -
      infiniteE P s (first s) * infiniteE P s (second s)) atTop
      (𝓝 (wakeFee F D L G (x - y) (x - y)))

theorem positionedCovarianceOnPooling (P : Spine) (gram : P.PhysicalWakeGram)
    (f : ℕ → ℕ) (β : ℕ → ℝ) (pool : Pooling P.run (takenVolume P) (takenCutoff P) f β) :
    PositionedStaffCovariance P β := by
  intro A hA x y separated F D L G r hr
  have first := (P.announces (A := A) 1 (by decide) hA 0 x).1
  have second := (P.announces (A := A) 1 (by decide) hA 0 y).1
  exact visit_book P hA first second gram pool F D L G hr separated

/-- One preparation and register, with the coupling family chosen before the
positions, plaquettes, spin components and staff depth. -/
theorem wakeElectionWithPositionedStaffCovariance (X : TintDemand) (Mc : ℕ) :
    ∃ (P : Spine) (K : P.Register) (E : ℝ),
      PreparedInvestment P K E Mc ∧ PureForce.CakeL.SignedPoseBudget P ∧
      QualifiedWakeReadout.{u} P K ∧ PhysicalWakeGram P ∧ PaidStaffCovariance P ∧
      ∀ f : ℕ → ℕ, StrictMono f → ∃ (c : ℕ → ℕ) (β : ℕ → ℝ), StrictMono c ∧
        Pooling P.run (takenVolume P) (takenCutoff P) (f ∘ c) β ∧
        PositionedStaffCovariance P β := by
  obtain ⟨P, K, E, investment, pose, readout, gram, covariance, funding⟩ :=
    wakeElectionWithPaidStaffCovariance.{u} X Mc
  refine ⟨P, K, E, investment, pose, readout, gram, covariance, ?_⟩
  intro f hf
  obtain ⟨c, β, hc, pool, _⟩ := funding f hf
  exact ⟨c, β, hc, pool, positionedCovarianceOnPooling P gram (f ∘ c) β pool⟩

/-- For the same two explicitly positioned staffs, the remaining selection
inputs are their two individual polls and their product poll. -/
theorem selectedPositionedStaffCovarianceOfPolls (P : Spine) (K : P.Register)
    (readout : QualifiedWakeReadout.{u} P K) (A : ℝ) (hA : 0 < A)
    (x y : Gaia) (separated : x ≠ y) (F D : PlaqAxes) (L G : Twah.DirSpin)
    (r : ℕ) (hr : 4 ≤ r) (f : ℕ → ℕ) (β : ℕ → ℝ)
    (pool : Pooling P.run (takenVolume P) (takenCutoff P) f β)
    (firstPoll : WakePoll P (positionedTest P A x F L r β) 0)
    (secondPoll : WakePoll P (positionedTest P A y D G r β) 0)
    (productPoll : WakePoll P (fun s =>
      positionedTest P A x F L r β s * positionedTest P A y D G r β s)
      (wakeFee F D L G (x - y) (x - y))) :
    ∃ c : ℕ → ℕ, StrictMono c ∧
      Pooling P.run (takenVolume P) (takenCutoff P) (f ∘ c) β ∧
      (∀ᶠ n : ℕ in atTop,
        let s := f (c n)
        (positionedTest P A x F L r β s).val =
          Papal.household P.calibration (positionedWeave P A x F L r β s) ∧
        (positionedTest P A y D G r β s).val =
          Papal.household P.calibration (positionedWeave P A y D G r β s)) ∧
      ∀ U : P.Spectrum0 3 → Prop, (∀ᵐ χ ∂P.pillars 3, U χ) →
      ∃ χ, U χ ∧ JointTuple.{u} P K χ ∧
        HoldRead P A (f ∘ c) χ x y (advice P A 1 0 x) (advice P A 1 0 y) ∧
        Tendsto (fun n =>
          let s := f (c n)
          let first := positionedTest P A x F L r β s
          let second := positionedTest P A y D G r β s
          P.singleState 3 s χ (first * second) -
            P.singleState 3 s χ first * P.singleState 3 s χ second) atTop
            (𝓝 (wakeFee F D L G (x - y) (x - y))) := by
  have first := (P.announces (A := A) 1 (by decide) hA 0 x).1
  have second := (P.announces (A := A) 1 (by decide) hA 0 y).1
  have paid := fitting_pair P hA first second F D L G (show A < A + 1 by linarith) hr
  have lease : P.PencilLease A x y (advice P A 1 0 x) (advice P A 1 0 y) :=
    ⟨first, second, fun same => (separated same).elim⟩
  exact selectedBookedStaffCovarianceOfPolls P K readout A hA x y
    (positionedStaff P A x F L) (positionedStaff P A y D G) (fun _ => r) β (A + 1) paid
    f pool lease (wakeFee F D L G (x - y) (x - y)) firstPoll secondPoll productPoll

end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

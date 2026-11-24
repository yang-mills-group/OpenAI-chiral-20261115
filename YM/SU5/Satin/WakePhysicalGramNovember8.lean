import SU5SatinWakeElectionNovember8
import YM.SU5.WindTorque.Clearance

set_option autoImplicit false
set_option synthInstance.maxSize 28000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter MeasureTheory
open scoped Topology
open Py Py.Rate LocalLimit Preparation Preparation.Yoke

namespace Spine
universe u

/-- The single and double staff estimates are evaluated on the physical
periods and cutoffs of this register's own coherent ground extension. -/
def PhysicalWakeGram (P : Spine) : Prop :=
  ∀ I : ℝ, 0 < I → ∀ᶠ s : ℕ in atTop, ∀ᶠ n : ℕ in atTop,
    Jewel.GramPace P.run s (P.period (P.projection.rows n))
      (P.cutoff (P.projection.columns n)) I

theorem wakeElectionWithPhysicalGram (X : TintDemand) (Mc : ℕ) :
    ∃ (P : Spine) (K : P.Register) (E : ℝ),
      PreparedInvestment P K E Mc ∧ PureForce.CakeL.SignedPoseBudget P ∧
      QualifiedWakeReadout.{u} P K ∧ PhysicalWakeGram P := by
  obtain ⟨P, K, E, investment, _, _, pose, readout⟩ := wakeElectionAndSignedPose.{u} X Mc
  refine ⟨P, K, E, investment, pose, readout, ?_⟩
  intro I hI
  obtain ⟨v, hv⟩ := investment.investment
  exact Jewel.onPermit (Y := P.run) (U := P.law) (Q := P.history)
    hv investment.dispatch investment.rocky.merit hI

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection


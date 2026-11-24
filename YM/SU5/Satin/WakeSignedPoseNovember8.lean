import SU5SatinBookedPhaseNovember8
import YM.SU5.WakeInvestment.Attempt

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Preparation.Yoke

namespace Spine
universe u

/-- Each admitted pair of layouts and countable family of poll readings uses a
single character for the current tuple, both layout estimates and all readings. -/
def QualifiedWakeReadout (P : Spine) (K : P.Register) : Prop :=
  ∀ (A : ℝ), 0 < A → ∀ (a b : Gaia) (u₁ w : ℕ → Cover)
      (J : Type) [Countable J] (f : ℕ → ℕ), StrictMono f →
      P.PencilLease A a b u₁ w →
      ∀ (R : J → ℕ → P.Test) (Z : J → ℂ), (∀ i, WakePoll P (R i) (Z i)) →
      ∃ c : ℕ → ℕ, StrictMono c ∧
        ∀ U : P.Spectrum0 3 → Prop, (∀ᵐ x ∂P.pillars 3, U x) →
        ∃ x, U x ∧ JointTuple.{u} P K x ∧ HoldRead P A (f ∘ c) x a b u₁ w ∧
          ∀ i, Tendsto (fun r => P.singleState 3 (f (c r)) x (R i (f (c r))))
            atTop (𝓝 (Z i))

/-- Buy both pose hypotheses at the election that prepares the marked current.
The layouts and limiting probes retain the qualifications of the CP2 estimate. -/
theorem wakeElectionAndSignedPose (X : TintDemand) (Mc : ℕ) :
    ∃ (P : Spine) (K : P.Register) (E : ℝ),
      PreparedInvestment P K E Mc ∧ Solstitial P.par ∧ Fountain P.par ∧
      PureForce.CakeL.SignedPoseBudget P ∧ QualifiedWakeReadout.{u} P K := by
  have purchase (n : ℕ) : CommissionVector (fun p =>
      ((TintRateCommercial n (crayon X) p ∧ Solstitial p) ∧ Meritorious p ∧
        15 ∣ p.R.L.val ∧ p.R.L.val % 16 = 1 ∧ 8 ∣ p.M.val) ∧ Solstitial p ∧ Fountain p) := by
    constructor
    intro e' ε he Q
    obtain ⟨P, ℓ, Z, Y, p', u', t', r, c, A, h, X', L', G', B', J⟩ :=
      (ministerFountain (crayon X) n).purchased e' ε he Q
    exact ⟨P, ℓ, Z, Y, p', u', t', r, c, A,
      ⟨⟨⟨h.1.1, h.1.2.1⟩, h.2⟩, h.1.2⟩, X', L', G', B', J⟩
  obtain ⟨P, K, E, eligibility, investment⟩ :=
    reappointed X (fun p => Solstitial p ∧ Fountain p) purchase Mc
  refine ⟨P, K, E, investment, eligibility.1, eligibility.2,
    PureForce.CakeL.endowment P eligibility.1 eligibility.2, ?_⟩
  intro A hA a b u₁ w J _ f hf lease R Z poll
  exact achet (P := P) (V := K) (p := hA) (a := a) (b := b) (u := u₁) (w := w)
    investment f hf lease R Z poll

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection


import YM.SU5.LoomForce.Stage3
import YM.SU5.May.LunarCheckpoint

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce
open Function Filter Metric Fock Finset Lat Lattice Next.Free Cube Tulip Scroll Spire Pastry RP Branch
  Wilson Phase SU Rush Mir Reflect Lifted Window Skye Dial Analysis MeasureTheory
open Lamour Lamour.Bridge Celeste Morn Hiro RG Girt
open Py Py.Rate Py.Rate.LocalLimit Preparation Yoke Papal Tapestry Journey Heat
open Ballad EmberWind CF.Pannier.Chancel WakeInvestment Jewel Shuttle
open YM.Stationary (Gaia)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology ContDiff Classical
open Palette
universe j

/-- The single-copy axial control uses the preparation and coupling of the mixed staff readings.
    Their elected character also carries the angular plate estimate. -/
theorem stage3WithAxialPriceAndAngularMotion (X : TintDemand) (Mc : ℕ) (A : ℝ) (hA : 0 < A) :
    ∃ (P : Spine) (K : P.Register) (E : ℝ) (u v : ℕ → Cover) (β : ℕ → ℝ) (f : ℕ → ℕ),
      PreparedInvestment P K E Mc ∧ PureForce.CakeL.SignedPoseBudget P ∧
      QualifiedWakeReadout.{j} P K ∧ PhysicalWakeGram P ∧
      PencilLease P A 0 touchPoint u v ∧ Pooling P.run (takenVolume P) (takenCutoff P) f β ∧
      (∀ s, |κFix β s| ≤ 2 * bornQ P.par s) ∧
      PaidPair P (A+1) (staffAt ∘ u) (staffAt ∘ v) (fun _ => 10) ∧
      (∀ s (U:ℕ → Cover), CovCover P.calibration (actorE P U A β s).val ∧
        InTest P.calibration true (skyDeck (nodeC (U s)) (10+8)) false (actorE P U A β s).val) ∧
      0 < ‖payoff‖ ∧ (∀ i,WakePoll P (pointVote P A u v β i) (meritTally i)) ∧
      Tendsto (fun s => unselectedCost P A u v s β) atTop (𝓝 payoff) ∧
      (∀ᶠ s : ℕ in atTop,
        ‖payoff‖ / 2 < ‖unselectedCost P A u v s β‖ ∧
        printedHere P.par P.width s (skyDeck (nodeC (u s)) (10+8)) (rescaledFit P s A 0 (1/4)) ∧
        printedHere P.par P.width s (skyDeck (nodeC (v s)) (10+8)) (rescaledFit P s A touchPoint (1/4)) ∧
        ∀ᶠ n in atTop, Ferry P.run s (takenVolume P (f n)) (takenCutoff P (f n)) ∧
          ShelterRent P.run s (takenVolume P (f n)) (takenCutoff P (f n)) ∧
          TiltInvoice P.run s (takenVolume P (f n)) (takenCutoff P (f n)) E) ∧ Sundial.Wrung P A f β E ∧
      ∀ (I : Type) [Countable I] (Z : I → ℕ → P.Test) (a : I → ℂ),
        (∀ i, WakePoll P (Z i) (a i)) → ∀ g : ℕ → ℕ, StrictMono g → ∃ c : ℕ → ℕ, StrictMono c ∧
          ∀ T : P.Spectrum0 3→Prop, (∀ᵐ x∂P.pillars 3,T x) → ∃ x, T x ∧ AngularMotion P x ∧ JointTuple.{j} P K x ∧
            HoldRead P A (g∘c) x 0 touchPoint u v ∧
            (∀ i, Tendsto (fun r=>P.singleState 3 (g (c r)) x (Z i (g (c r)))) atTop (𝓝 (a i))) ∧
            (∀ i, Tendsto (fun r=> P.singleState 3 (g (c r)) x (pointVote P A u v β i (g (c r)))) atTop
              (𝓝 (meritTally i))) ∧
            Tendsto (fun r=>coupleP P x u v A β (g (c r))) atTop (𝓝 payoff) ∧
            ∀ᶠ r in atTop, ‖payoff‖/2 < ‖coupleP P x u v A β (g (c r))‖ := by
  obtain ⟨P, K, E, u, v, β, f, invest, pose, readout, gram, layout, pooling,
    coupling, pair, domains, nonzero, polls, unselected, prices, axial, elect⟩ := stage3.{j} X Mc A hA
  refine ⟨P, K, E, u, v, β, f, invest, pose, readout, gram, layout, pooling,
    coupling, pair, domains, nonzero, polls, unselected, prices, axial, ?_⟩
  intro I instI Z a hZ g hg
  obtain ⟨c, hc, electOn⟩ := elect I Z a hZ g hg
  refine ⟨c, hc, ?_⟩
  intro T hT
  obtain ⟨x, hx, joint⟩ := electOn T hT
  exact ⟨x, hx, AngularEarned P x, joint⟩

end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce

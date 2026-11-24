import SatinPhysicalSmearsReview
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

/-- The connected reading of the actual shrinking fronts has zero limit on the
very same fixed tests. Centering uses the actual elected one-point readings. -/
theorem ThinFrontReadings.connected {P : Spine} {x : P.Spectrum0 3}
    {c r : ℕ → ℕ} {F G : SampleDose} (h : P.ThinFrontReadings x c r F G)
    (Z W : Lead.Clan) (t : ℕ → ℕ) (ht : Tendsto t atTop atTop)
    (fine : ∀ i, c i ≤ t i) :
    let U := fun i => P.thinIncoming Z (c i) (r i) (t i) F
    let V := fun i => P.thinOutgoing W (c i) (r i) (t i) G
    Tendsto (fun i => P.singleState 3 (t i) x (U i * V i) -
      P.singleState 3 (t i) x (U i) * P.singleState 3 (t i) x (V i)) atTop (𝓝 0) := by
  obtain ⟨_, joint, left, right, _⟩ := h Z W t ht fine
  simpa only [sub_self] using joint.sub (left.mul right)

/-- Comparing against a product of the elected pure marginals, rather than
centering within the actual state, gives a nonzero limiting discrepancy. -/
theorem ThinFrontReadings.rawDiscrepancy {P : Spine} {x : P.Spectrum0 3}
    {c r : ℕ → ℕ} {F G : SampleDose} (h : P.ThinFrontReadings x c r F G)
    (Z W : Lead.Clan) (t : ℕ → ℕ) (ht : Tendsto t atTop atTop)
    (fine : ∀ i, c i ≤ t i) (X : ℕ → P.Test →ₗ[ℂ] ℂ)
    (hX : ∀ᶠ i : ℕ in atTop, P.SameRawProduct (t i) x (X i)) :
    let U := fun i => P.thinIncoming Z (c i) (r i) (t i) F
    let V := fun i => P.thinOutgoing W (c i) (r i) (t i) G
    (purePrice Z : ℂ) * (purePrice W : ℂ) ≠ 0 ∧
    Tendsto (fun i => P.singleState 3 (t i) x (U i * V i) - X i (U i * V i))
      atTop (𝓝 ((purePrice Z : ℂ) * (purePrice W : ℂ))) := by
  obtain ⟨ne, joint, _, _, factors⟩ := h Z W t ht fine
  refine ⟨ne, joint.congr' ?_⟩
  filter_upwards [factors, hX] with i hg hx
  simp only [(hg (X i) hx).2.2, sub_zero]

/-- All two-by-two minors of the limiting six-channel raw matrix vanish. -/
theorem thinFrontPriceMinors (A B C D : Lead.Clan) :
    ((purePrice A : ℂ) * purePrice C) * (purePrice B * purePrice D) -
    ((purePrice A : ℂ) * purePrice D) * (purePrice B * purePrice C) = 0 := by ring

#print axioms ThinFrontReadings.connected
#print axioms ThinFrontReadings.rawDiscrepancy
#print axioms thinFrontPriceMinors
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

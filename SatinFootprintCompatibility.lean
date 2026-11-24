import YM.SU5.Relativistic.Box
import YM.SU5.Reconstruct.Effective

/-! Compare the closed-ball footprint of the real-position chart with the earlier
coordinate collar, including every point of the finite physical support. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 270000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Tapestry Tapestry.Altitude PhaseChoice

open Selected
variable (Λ : Preparation) (l s : ℕ)

theorem chartBall_eq_collar (x : Cover) :
    Metric.closedBall (PhaseChoice.location Λ s x) (Journey.reserve Λ l * Selected.gaugeMesh Λ s) =
      collar Λ l s x := by
  ext y
  rw [box_iff, shield_collar]
  change (fun i : Axis => (2*y i)/2) ∈ collar Λ l s x ↔ y ∈ collar Λ l s x
  have same : (fun i : Axis => (2*y i)/2) = y := by funext i; ring
  rw [same]

theorem realChartFootprint_eq_collarFootprint (S : Finset Cover) :
    realChartFootprint Λ l s S = footprint Λ l s S := by
  simp only [realChartFootprint, footprint, chartBall_eq_collar, Finset.mem_coe]

#print axioms chartBall_eq_collar
#print axioms realChartFootprint_eq_collarFootprint
end YM.CF.Buffered.Afterglow.Tower.Reconstruction

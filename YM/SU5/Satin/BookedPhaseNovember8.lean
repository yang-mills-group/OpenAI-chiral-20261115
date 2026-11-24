import SU5SatinCurrentNovember8

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option maxRecDepth 2000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
namespace PureForce
namespace CakeL
open Branch Hake Hive Pose Products WickLabels Bill Material Third Vessel Stars Set

variable (P : Spine)
local notation "Λ" =>P.par
local notation "Γ" =>P.run
local notation "cA" => ((Λ).d+(Λ).J.roomX)/2
local notation "nnB" s:max i:max=> Papal.count (Γ) s i
local notation "fB" s:max i:max k:max=> (Papal.gram (Γ) s i k).J

/-- The full scalar and kernel budget in the signed-pose endowment. -/
def SignedPoseBudget : Prop :=
  ∃ z a C:ℝ, 0<z∧0<a∧0<C∧∀ s:ℕ,∀ᶠ i:ℕ in atTop,∀ k:ℕ,s≤ (Γ).uv k→
    (Pose.Products.License (nnB s i) (fB s i k) (Λ).K.j (2*z) cA (Λ).d a C) ∧
    (∀ x:Orbit (nnB s i), Cube.Guard (Papal.room (Γ) s i x) cA) ∧
    ∀ (e:gaugeLink (nnB s i))(b:Bool),∃ (Y:Seal (Seat (nnB s i))→ Pose.Test (nnB s i) cA z→ℂ)(D:Seal (Seat (nnB s i))→ℝ),
      (∀ S:Seal (Seat (nnB s i)),Bill.Tag (Pose.H (nnB s i) cA z) (tollZ cA z) (Skye.ends e) S (Y S) (D S)) ∧
      (∑ S:Seal (Seat (nnB s i)),Branch.rent a S *D S)≤C ∧
      ∀ x,phasef (m:=Vale.mesh ((Γ).ir i) P.par.R.L s) (Λ).U (fB s i k) e b z cA x = 1+∑ S,Y S x

end CakeL
end PureForce
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

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
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus

open QuadClock Preparation.Yoke

namespace Spine
universe u

/-- The selection supplying the registered construction also discharges the
two eligibility hypotheses of the signed-pose budget, on that same spine. -/
theorem bookedSignedPoseBudget (n : ℕ) (hn : (2 : ℝ) * Ione.strive_E 6 ≤ (n : ℝ))
    (X : TintDemand) (Y : Supplier) (L M : ℝ) (hM : 0 < M) :
    ∃ (P : Spine) (K : P.Register),
      uniform P K Y L M ∧ P.Roster ∧ P.NightCop ∧
      TintRateCommercial n (crayon X) P.par ∧ Solstitial P.par ∧ Fountain P.par ∧
      PureForce.CakeL.SignedPoseBudget P := by
  obtain ⟨P, K, hu, hr, hn', eligibility, _⟩ := bookedFV n hn X Y L M hM
  exact ⟨P, K, hu, hr, hn', eligibility.1, eligibility.2.1, eligibility.2.2,
    PureForce.CakeL.endowment P eligibility.2.1 eligibility.2.2⟩

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

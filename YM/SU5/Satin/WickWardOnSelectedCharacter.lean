import ForceSatinCP4
import YM.SU5.May.TorqueCP

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 3200
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ
open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers
open CF.Papyrus.Franc.Loaves
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay

/-- The character chosen for the funded Wick-kernel comparison also carries the booked
Ward transport estimate on that same spine. The character retains the original
quantifiers over eligible paths and full-measure selection conditions. -/
theorem sameHessElectionWithWard (M L : ℕ) (d h' βmin : ℝ) (hd : 0 < d) :
    ∃ (P : Spine) (K : P.Register) (n:ℕ) (b C : ℝ) (bare_ : ℕ → ℝ),
      2*strive_E 6 < (n:ℝ) ∧ L ≤ P.par.R.L.val ∧ P.par.R.L.val%16=1 ∧ 15 ∣ P.par.R.L.val ∧
      TintCommercial n (crayon (fun _ _ _ _ _ _=>0)) P.par ∧ Solstitial P.par ∧
      Rocky P K M ∧ CathedralQ P ∧ SingleRootFinance P ∧ LitFuture P M ∧
      P.UnderLease P.jump128 0 ∧ h' ≤ P.par.h ∧ P.par.d ≤ d ∧ βmin < P.par.x ∧
      ∀ S:ℕ→ℕ, StrictMono S → ∃ (U:ℕ→ℕ)(W:ℕ→HorizonLens→HorizonLens→ℝ)(β:ℕ→ℝ), StrictMono U ∧
      CouncilGrant P K b C bare_ (S ∘ U) W β ∧ PublicKernel P (S ∘ U) W ∧
      ∀ good:P.Spectrum0 3→Prop, (∀ᵐ x ∂P.pillars 3,good x) → ∃ x, good x ∧ JointTuple.{uΩ} P K x ∧ P.AngleWages x := by
  obtain ⟨P, K, n, b, C, bare, large, size, residue, multiple, tint, solstitial,
    rocky, cathedral, finance, future, lease, height, mesh, coupling, paths⟩ :=
    sameHessElection M L d h' βmin hd
  refine ⟨P, K, n, b, C, bare, large, size, residue, multiple, tint, solstitial,
    rocky, cathedral, finance, future, lease, height, mesh, coupling, ?_⟩
  intro S increasing
  obtain ⟨U, W, β, refined, grant, kernels, elect⟩ := paths S increasing
  refine ⟨U, W, β, refined, grant, kernels, ?_⟩
  intro good fullMeasure
  obtain ⟨x, eligible, joint⟩ := elect good fullMeasure
  exact ⟨x, eligible, joint, P.sails_angle x⟩

end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

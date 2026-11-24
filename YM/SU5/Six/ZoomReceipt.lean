import VerifiedSatinWidthAndUVNovember4
import YM.SU5.Six.Provider
import YM.SU5.Six.ZoomGram

/-!
# Public interface: six-clan matrix zoom (`l:zoommat`)
-/
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

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

namespace Spine
open Cheer YM.Six

/-- M in this application. Common across axes via `single_agrees`. -/
abbrev sixM (P : Spine) (x : P.Spectrum0 3) (s : ℕ) : P.Test →ₗ[ℂ] ℂ := P.singleState 3 s x

variable (P : Spine) (x : P.Spectrum0 3) (c r : ℕ → ℕ)
local notation "ξ" => P.otherSpectrum 3 3 x
local notation "ρ" i:max => P.dew (c i) (r i)

lemma sixM_axes (j : Axis) (s : ℕ) (F : P.Test) :
    P.singleState j s (P.otherSpectrum 3 j x) F = P.sixM x s F :=
  P.single_agrees 3 j x s F

/-- Statement in terms of the LIVE charging convention on the tested
continuous part. `Z` indexes `Window.Family = Fin 3 × Bool`. Axis 3;
frequency half-space; radian; complex inner star-in-FIRST. `pairIntegral`
(read via `bill`) handles the off diagonals, see `Spectral.PVM` API under
`YM/SU5/Six`. -/
structure SixZoom : Prop where
  v0 (Z : Window.Family) (s n : ℕ) :
    P.birthCloud x Z s n =
      P.wealth 3 ξ (P.viewF 3 ξ s (P.brightC Z s n)) -
      P.sixM x s (P.stockS Z (P.flash n)) • P.heaven 3 ξ
  shrinking : Tendsto (fun i => ρ i) atTop (𝓝 0)
  positive (i : ℕ) : 0 < ρ i
  integrals {F : ℕ → E4 → ℂ} {f : E4 → ℂ} (h : HalfLimit F f) :
    Tendsto (fun i => P.zoomBill x (c i) (r i) (F i)) atTop
      (𝓝 (Matrix.diagonal fun Z => ∫ p, f p ∂(promenade Z:Measure E4)))
  bands (V : Set E4) (h : IsOpen V) (hv : (Mink.inside ∩ V).Nonempty) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ i in atTop, d • (1 : Matrix Window.Family Window.Family ℂ) ≤
      P.windowCharge x (c i) (r i) V


variable {P x c r}

/-- Matrix zoom on this phase. -/
theorem SixElection.zoom {K : P.Register} (H : P.SixElection K x c r) : P.SixZoom x c r := by
  constructor
  · exact fun Z s n => congrArg (fun a : ℂ => P.lucid x Z s n - a • P.heaven 3 ξ)
        (P.sixM_axes x 3 s (P.stockS Z (P.flash n)))
  · exact proper_dew P c r H.launch
  · exact fun i => P.dew_pos _ (H.launch.unitSize i)
  · exact fun h => zoom_matrix H.launch H.ready keyV_go H.star_carrier h
  · exact fun _ h hv => uniform_charge H.launch H.ready keyV_go H.star_carrier h hv

#check @install_for_Six
#print axioms install_for_Six
#check @elect_for_Six
#print axioms elect_for_Six
#check @SixElection.zoom
#print SixZoom
#print axioms SixElection.zoom
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

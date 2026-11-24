import Preen.Status
import CellQ.Misty
import Preen.Travel
import GlazeS.Incline
import GlazeS.Room
import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
set_option maxRecDepth 6000
set_option maxHeartbeats 140000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open Py.Rate.Pitching.Focus
open _root_.YM.Preen
open Py.Dyad Keeping
variable (P:Spine)(M:Morn P.par.K)(α:ℝ)(F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3)(p:∀ s,F ≤ s→ Accordance P M F s (C s) (D s))
local notation "ξ"=>P.otherSpectrum 3 3 x
local notation "Ω"=>P.heaven 3 ξ
local notation "ζ"=>P.wealth 3 ξ
local notation "ϕ"=>paster (Ω)
variable (t:Jones P M α F C D x)
include t
lemma jBridge : Jones P M α F C D (ξ) :=by
 filter_upwards [t] with d h j k n b
 have he:=h k b
 apply (pow_le_pow_iff_left₀ (norm_nonneg _) ((norm_nonneg _).trans he) (n:=2) (by norm_num)).mp
 rw [←as_paid]; unfold readingSq; rw [P.single_agrees]; rw [←show _=(P.singleState 3 (n+1) x _).re from (rfl : readingSq ..= _), as_paid]; exact pow_le_pow_left₀ (norm_nonneg _) he _
def brokerM:(P.ColorHil 3 (P.otherSpectrum 3 3 x)).space→L[ℂ] (P.ManyF 3 (P.otherSpectrum 3 3 x)).space:= (ϕ).comp ζ
omit t in
private lemma fuseHm {X Y:Hilbert}(f:Y.space→L[ℂ]Y.space)(g:X.space→L[ℂ]Y.space)(h:‖f‖≤1)(u:‖g‖≤1):‖f.comp g‖≤1:= (ContinuousLinearMap.opNorm_comp_le f g).trans (mul_le_one₀ h (norm_nonneg _) u)
include p t
lemma vergeH : ∀ᶠ d:ℕ in atTop, let j:=hikeV d; idle P F C D ξ j →∀ k:ℕ, ‖brokerM P x (sparrow P F ξ (j+k) j)‖ ≤2*((2/ThinGauge.boost (Xη P.par.R.L))^k*(2^d*(2*ranch P M α j))) :=by
 let A:=brokerM P x
 have hp: ‖A‖≤1:= fuseHm _ _ (pasted_cost _) (P.enter_wealth ..)
 filter_upwards [annihilates P M F C D ξ (jBridge P M α F C D x t) (V:=(P.ManyF 3 ξ).space) (fun s h=> (p s h).1)] with d he j t k
 exact he A hp t k
#print axioms vergeH
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

import YM.SU5.Six.Zoom
import YM.SU5.Six.FrameBound
set_option maxHeartbeats 250000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option quotPrecheck false
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
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open OS.Semigroup (F)
open OS.Semigroup.Balloon
open Cheer
open Cheer (Narrow)
variable (P:Spine)(x:P.Spectrum0 3)(s n:ℕ)(c r:ℕ→ℕ)(z:SixCoefficients)
local notation "S"=> P.seasons 3 (P.otherSpectrum 3 3 x)
local notation "H"=> P.ManyF 3 (P.otherSpectrum 3 3 x)
def spectralRoster (s n:ℕ) (V:Set E4) (Z:Lead.Clan): H:=
  (S).ℚmeasure.region (press (P.dew s n) V) (P.birthCloud x Z s n)
lemma diagonalLimit_pos (hn:z≠0)(V:Set E4)(h:IsOpen V)(p:(Mink.inside ∩ V).Nonempty) :
    0 < (diagonalLimit z:Measure E4) V:= by
  obtain ⟨Z,v⟩:∃ Z:Lead.Clan, z Z≠0:= by
    by_contra! ht
    exact hn (funext ht)
  have hv:0<‖z Z‖₊^2:= pow_pos (nnnorm_pos.mpr v) _
  unfold diagonalLimit
  rw [FiniteMeasure.toMeasure_sum,Measure.finsetSum_apply]
  refine lt_of_lt_of_le ?_ (single_le_sum (fun i _=> (show 0≤ ((‖z i‖₊^2 • promenade i: Narrow):Measure E4) V from bot_le)) (mem_univ Z))
  exact ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr hv.ne') (importance Z h p).ne'
variable {P x c r} {q:ℕ→ℝ}
  (A:Launch P c r)(Y:readyUV P c r x q)(hq:Tendsto q atTop (𝓝 0))(u:P.lodestarHere 3 (P.otherSpectrum 3 3 x))
local notation "ρ" i:max=> P.dew (c i) (r i)
include A Y hq u
lemma roster_one_bound (Z:Lead.Clan)(V:Set E4)(h:IsOpen V) :
    Limited H (fun i=> P.spectralRoster x (c i) (r i) V Z):= by
  let v(i):= P.birthCloud x Z (c i) (r i)
  let f(i):= Cheer.outlay (S) (v i) (ρ i)
  have hx:Tendsto (fun i:ℕ=>( (f i).mass:ℝ)) atTop (𝓝 ((promenade Z).mass:ℝ)):=
    (lyricalCloud Z A Y hq u).massR
  let d:ℝ:= ((promenade Z).mass:ℝ)+1
  refine ⟨Real.sqrt d,?_⟩
  filter_upwards [hx.eventually (ge_mem_nhds (lt_add_one _))] with i w
  have he: ((f i:Measure E4)).real V ≤ (f i).mass:= measureReal_mono (μ:=(f i:Measure E4)) (Set.subset_univ _)
  exact Real.le_sqrt_of_sq_le ((norm_region (S) _ (ρ i) V h.measurableSet).le.trans (he.trans w))

/-- `l:zoommat` spectral projection estimate, in PSD (quadratic form) order.
 Works also on any open band with a point in the cone interior.
 `press` tests the *scaled* band at each i. -/
theorem zoomMatrix_floor (V:Set E4)(h:IsOpen V)(p:(Mink.inside∩V).Nonempty) :
    ∃ d:ℝ,0<d∧∀ᶠ i in atTop, FrameBound.Coercive Lead.Clan H
      (P.spectralRoster x (c i) (r i) V) d:= by
  refine FrameBound.eventual Lead.Clan H (fun i=> roster_one_bound A Y hq u i V h) ?_
  intro a w
  let b:ℝ:= ((diagonalLimit a):Measure E4).real V
  have he:= diagonalLimit_pos a w V h p
  have ht:0<b:= ENNReal.toReal_pos he.ne' (measure_ne_top _ _)
  have hz:(diagonalLimit a:Measure E4)≠0:= by intro e; rw [e] at he; exact lt_irrefl _ he
  refine ⟨b/2,half_pos ht,?_⟩
  filter_upwards [knock _ V (FLap_zoomMatrix a A Y hq u) hz h (half_lt_self ht)] with i v
  exact lt_of_lt_of_eq v (P.zoom_matrix_event x (c i) (r i) a V h.measurableSet)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

import ExactRunning.Calc.Quad
import ExactRunning.Endpoints.Stable
import ExactRunning.Thermo.SlabPole

/-!
# Finite part control

Use the single peeled (`Endpoint.price`) integrand for all our IR cuts.
As d ↓ 0:
* for endpoints from `harvest`, get bounded finite part on native
  cut, uniformly in endpoint (`finite_part`). Compare to archive's
  logarithmic pole by taking μ ↓ 0 in the pointwise singularity
  estimates.
* For use with overlap of consecutive step regulators: coming back
  from a fine cut to a native cut (removing extra masking on aliases)
  makes negligible difference (`correction`), where the convergence
  need not be uniform.

No claim of convergence of the individual finite part needed.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
variable {G : Gauge} {R : PathData G} {p : Clip} {m : Side} {F : KindF G}

open MeasureTheory

variable {A C d : ℝ} {D : Latitude}

lemma Latitude.Medium.mag_smooth {F : Scene (Entry G)} (h : D.Medium F) (i : G.ColorIndex) :
    ContDiff ℝ ∞ (magcurve (D.run F) i) :=
  h.smooth (tilt_smooth 0) (tilt_real 0) (tilt_quiet D (by decide: (0:Axis) ≠ 3)) _ _

namespace Endpoint
variable (s : Endpoint p R F)
include s

lemma price (hd : 0<D.radius) (i : G.ColorIndex) :
    epValue F D i = (D.mean (peeled F i)).re := by
  have h := s.medium hd
  rw [epValue,alphaK,quad_re ((h.mag_smooth i).contDiffAt.of_le (by decide))]
  unfold magcurve
  rw [h.peel (tilt_smooth 0) (tilt_real 0) (tilt_quiet D (by decide:(0:Axis) ≠ 3))]
  rfl

lemma integrable (hd : 0<D.radius) (i : G.ColorIndex) :
    IntegrableOn (peeled F i ∘ tap) D.region volume :=
  D.integrableOn fun _ hx =>
    (((s.medium hd).line (tilt_smooth 0) (tilt_real 0)
      (tilt_quiet D (by decide: (0:Axis) ≠ 3)) (stripe i) (stripe i)).quad_regular _ hx).continuousAt

lemma correction (L : Side) (i : G.ColorIndex) :
    Tendsto (fun d:ℝ=> epValue F (Latitude.native d) i - epValue F (Latitude.incoming L d) i)
      (𝓝[>] 0) (𝓝 0) := by
  refine ((Complex.continuous_re.tendsto _).comp
    (Latitude.tendsto_native_sub L (f:=peeled F i)
      (fun d hd => s.integrable (show 0<(Latitude.native d).radius from hd) i))).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with d hd
  rw [s.price (show 0<(Latitude.native d).radius from hd),
      s.price (show 0<(Latitude.incoming L d).radius from mul_pos (side_pos L) hd),
      Function.comp_apply, Complex.sub_re]

lemma singular (h : Grounds A C F) (hd : 0<d) (i : G.ColorIndex)
    (x) (hx : x∈(Latitude.native d).region) :
    ‖peeled F i (tap x)‖ ≤ A/‖x‖^4 ∧
    ‖peeled F i (tap x) - ↑(poleVec G (exileE x))‖ ≤ C/‖x‖^3 := by
  have hfront : FrontBox (exileE x) := cradleFront _ hx.1
  have hn : 0<‖x‖ := by
    rw [norm_pos_iff]
    intro hv
    have hh := hx.2
    rw [Latitude.active, Latitude.native_cradle hx.1, hv] at hh
    exact (show d<0 from by simpa [Latitude.native] using hh).not_ge hd.le
  let X (μ : ℝ) := keelRay (amena μ G F) i (exileE x)
  have ht : Tendsto X (𝓝[>] 0) (𝓝 (peeled F i (tap x))) :=
    s.tendsto_keel _ (shade_of_safe (Latitude.native d) hd (tap_real _) hx.2.safe) _
  constructor
  · have hz : Tendsto (fun μ : ℝ=> A/(‖x‖+μ)^4) (𝓝[>] 0) (𝓝 (A/‖x‖^4)) := by

      have hu : ContinuousAt (fun μ : ℝ => A/(‖x‖+μ)^4) 0 := by fun_prop (disch := positivity)
      simpa using hu.tendsto.mono_left (nhdsWithin_le_nhds (s:=Set.Ioi 0))
    refine le_of_tendsto_of_tendsto ht.norm hz ?_
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
      (ge_mem_nhds (show (0:ℝ)<1 from zero_lt_one))] with μ hh hp using
      (h hh hp i).1 _ hfront
  have hz : Tendsto (fun μ:ℝ => C/‖x‖^3+C*μ^2/‖x‖^6) (𝓝[>] 0) (𝓝 (C/‖x‖^3)) := by
    have hu : ContinuousAt (fun μ:ℝ=> C/‖x‖^3+C*μ^2/‖x‖^6) 0 := by fun_prop (disch := positivity)
    simpa using hu.tendsto.mono_left (nhdsWithin_le_nhds (s:=Set.Ioi 0))
  refine le_of_tendsto_of_tendsto (ht.sub_const _ |>.norm) hz ?_
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (ge_mem_nhds (show (0:ℝ)<1 from zero_lt_one)),mem_nhdsWithin_of_mem_nhds
    (ge_mem_nhds hn)] with μ hh hp hμ using
    (h hh hp i).2 _ hfront hμ

lemma finite_part (h : Grounds A C F) (ha : 0≤A) (hc : 0≤C)
    (hd : 0<d) (hle : d≤1) (i : G.ColorIndex) :
    |epValue F (Latitude.native d) i + G.slopeConstant * Real.log d⁻¹| ≤ SlabPole.charge G A C := by
  rw [s.price hd (D:=.native d)]
  exact SlabPole.absoluteLatitude G hd hle ha hc (s.integrable hd _)
    (fun x y => (s.singular h hd i x y).1)
    (fun x y => (s.singular h hd i x y).2)
end Endpoint

end ExactRunning

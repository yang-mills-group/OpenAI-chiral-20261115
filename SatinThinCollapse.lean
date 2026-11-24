import SatinFixedContrastNovember4

/-!
# A thin bilocal-composite experiment: I. positive physical time estimate

Use the *front* mat of the six-channel experiment. `shard` is its view vector;
`lucid` its continuous-space projection. The scale factor is exactly the one in
that experiment before differencing front minus back. **No mean subtraction**
in the new probes. This choice matters. In fact we prove what happens here
*also* for the mean-subtracted fields (compare the argument for loss of
propagation in `the construction notes`).

Use only the actual elected character and Experiment hypotheses purchased
from the project. We go from a *zoom* comparison on this x, with
correlations at shrinking distances, to an answer, including strong
convergence in the physical Hilberts, on tests at distances bounded below
by arbitrary positive **physical** constants. In fact the pointwise norm
estimate works for gaps growing without bound *relative to dew*.

This is for Euclidean one- and two-point fields (smeared fields on the
vacuum). See application for interaction criterion. Not a claim of
convergence on coincident products, multibody vector convergence, an
operator on a Wightman domain, or a propagating connected signal between
the two boxes.
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon

-- As in the diagonal FLap computation in Six/AnchorPos. Now seen to arbitrary
-- precision with sufficiently *large* zoom heat. No uniformity in the zoom theorem
-- at these changing heat prices needs to be assumed!
lemma thin_zoom_comparison_decay (Z : Lead.Clan) :
    Tendsto (fun n : ℕ => Cheer.FLap (promenade Z) 0 (↑(n : ℝ))) atTop (𝓝 0) := by
  let M : Measure E4 := (promenade Z : Measure E4)
  let f (n : ℕ) := Cheer.tendsK (0 : Space3) ((n : ℝ) : ℂ)
  letI : IsFiniteMeasure M := (promenade Z).property
  have ev (n : ℕ) (p : E4) : f n p = (Real.exp (-((n:ℝ)*YM.time p)) : ℂ) := by
    unfold f Cheer.tendsK; push_cast; simp
  have dec : ∀ᵐ p ∂M, Tendsto (fun n => f n p) atTop (𝓝 ((fun _ : E4 => (0:ℂ)) p)) := by
    filter_upwards [promenade_strict Z] with p hp
    have ht : 0 < YM.time p := ((Mink.strict_self _).1 hp).1
    simp_rw [ev]; exact Complex.continuous_ofReal.continuousAt.tendsto.comp
      (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (tendsto_natCast_atTop_atTop.atTop_mul_const ht)))
  have t := tendsto_integral_filter_of_dominated_convergence (F:=f) (μ:=M) (fun _ => (1:ℝ))
    (Eventually.of_forall fun n => (Cheer.airy ..).aestronglyMeasurable)
    (Eventually.of_forall fun n => (promenade_strict Z).mono (fun p h =>
      Cheer.withinK 0 ((n:ℝ):ℂ) p (by simp) (((Mink.strict_self _).1 h).1.le)))
    (integrable_const (1:ℝ)) dec
  rw [integral_zero] at t; exact t

private theorem thin_e_twice {Y : Hilbert} {j : Axis} (T : OS.Semigroup Y j)
    (y : Y) (t u : ℝ≥0) (p : t=u+u) : (inner ℂ y (T.U 0 (T.E t y))).re=‖T.E u y‖^2 := by
  rw [T.uZero, ContinuousLinearMap.id_apply, p, T.time, ContinuousLinearMap.comp_apply,
    ←OS.Semigroup.swing, ←inner_self_eq_norm_sq (𝕜:=ℂ)]
  rfl

section
variable (Z : Lead.Clan) {P : Spine} {c r : ℕ → ℕ} {x : P.Spectrum0 3}
  {K : P.Register} {J : P.Ellis 3 x} (B : Experiment P K c r x J)
local notation "ξ" => P.advocate 3 x 3
local notation "Ψ" => P.seasons 3 ξ
local notation "H" => P.ManyF 3 ξ
local notation "R" => P.physicalEnergy 3 ξ
local notation "G" => P.ColorHil 3 ξ
local notation "E" => (Ψ).E
local notation "ρ" i:max => P.dew (c i) (r i)
local notation "ϕ" i:max => P.birthCloud x Z (c i) (r i)
local notation "λ'" => (P.enter 3 ξ)
local notation "z" => ((purePrice Z : ℝ) : ℂ)
local notation "ω" => P.colorZero 3 ξ
local notation "Ω" => P.heaven 3 ξ
include B

/-- A scaling test on actual heat-norms. -/
lemma thin_norm_zoom_compare (n : ℕ) :
    let d (i : ℕ) : ℝ≥0 := ⟨ρ i, (P.dew_pos _ (B.launch.unitSize i)).le⟩
    Tendsto (fun i => ‖E (d i * ((n:ℝ≥0)/2)) (ϕ i)‖^2) atTop
      (𝓝 (Cheer.FLap (promenade Z) 0 (↑(n:ℝ))).re) := by
  intro d
  have hd (i : ℕ) : (d i : ℝ) = ρ i := rfl
  let T (i : ℕ) := d i * (n:ℝ≥0)
  have he : P.dimensionS c r T (n:ℝ) := tendsto_const_nhds.congr fun i => by
    rw [show (T i:ℝ)=ρ i * (n:ℝ) from by unfold T; rw [NNReal.coe_mul,NNReal.coe_natCast,hd]]
    field_simp [(P.dew_pos _ (B.launch.unitSize i)).ne']
  let p (i : ℕ) := (0:Bank)
  have hp : Tendsto (fun i => (ρ i)⁻¹ • p i) atTop (𝓝 (cutPulse 0)) := by
    rw [show cutPulse 0=0 from Subtype.ext (show position (0:Space3) 0=0 from
      (by rw [←Mink.combine_at]; exact map_zero _))]; simpa only [p, smul_zero] using (tendsto_const_nhds (x:=(0:Bank)))
  let X (i : ℕ) := E (d i * ((n:ℝ≥0)/2)) (ϕ i)
  have h (i : ℕ) : (inner ℂ (ϕ i) ((Ψ).U (p i) (E (T i) (ϕ i)))).re=‖X i‖^2 :=
    thin_e_twice Ψ (ϕ i) (T i) (d i*((n:ℝ≥0)/2)) (by rw [←mul_add,add_halves])
  have hv:=zoom_diagonal Z B.launch B.ready Twah.keyV_go (B.ground.2.1.accepted 3) (0:Space3) ⟨(n:ℝ), (Nat.cast_nonneg n)⟩ _ he _ hp
  exact (Complex.continuous_re.continuousAt.tendsto.comp hv).congr h

/-- Loss of the *centered* front mark, in the very same Color-continuous Hilbert.
Applies even while probing at a scale tending to zero, if large compared to dew. -/
lemma thin_dew_loss (t : ℕ → ℝ≥0) (h : Tendsto (fun i => (t i:ℝ)/(ρ i)) atTop atTop) :
    Tendsto (fun i => E (t i) (ϕ i)) atTop (𝓝 0) := by
  let d (i : ℕ) : ℝ≥0 := ⟨ρ i,(P.dew_pos _ (B.launch.unitSize i)).le⟩
  have hd (i : ℕ) : (d i : ℝ) = ρ i := rfl
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := ((Complex.continuous_re.continuousAt.tendsto.comp
    (thin_zoom_comparison_decay Z)).eventually (gt_mem_nhds (show (0:ℂ).re < ε^2 from
      (show 0 < ε^2 from pow_pos hε 2)))).exists
  have hn' : (Cheer.FLap (promenade Z) 0 (↑(n:ℝ))).re < ε^2 := hn
  let u (i : ℕ) := d i*((n:ℝ≥0)/2)
  filter_upwards [(show Tendsto (fun i:ℕ => ‖E (u i) (ϕ i)‖^2) atTop
          (𝓝 (Cheer.FLap (promenade Z) 0 (↑(n:ℝ))).re) from thin_norm_zoom_compare Z B n).eventually (gt_mem_nhds hn'),
        h.eventually (eventually_ge_atTop ((n:ℝ)/2))] with i hn v
  have he : u i ≤ t i := by
    apply (NNReal.coe_le_coe).mp
    simp only [u, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast,NNReal.coe_ofNat,hd]
    rw [mul_comm]; exact (le_div_iff₀ (P.dew_pos _ (B.launch.unitSize i))).1 v
  change dist (E (t i) (ϕ i)) 0 < ε
  rw [dist_zero_right]
  exact ((Ψ).norm_decrease _ he).trans_lt ((sq_lt_sq₀ (norm_nonneg _) hε.le).mp hn)

lemma thin_compare_dew {a : ℝ≥0} (ha : 0 < a)
    (t : ℕ → ℝ≥0) (h : ∀ᶠ i in atTop, a ≤ t i) :
    Tendsto (fun i => (t i:ℝ)/(ρ i)) atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro m
  have p : Tendsto (fun i => m*(ρ i)) atTop (𝓝 0) := by
    simpa using (P.proper_dew c r B.launch).const_mul m
  filter_upwards [p.eventually (ge_mem_nhds (show (0:ℝ) < a from ha)), h] with i v l
  exact (le_div_iff₀ (P.dew_pos _ (B.launch.unitSize i))).2 (v.trans (show (a:ℝ) ≤ t i from l))

lemma thin_front_lucid_tendsto (t : ℕ → ℝ≥0)
    (h : Tendsto (fun i => (t i:ℝ)/(ρ i)) atTop atTop) :
    Tendsto (fun i => E (t i) (P.lucid x Z (c i) (r i))) atTop (𝓝 (z • Ω)) := by
  have ht : Tendsto (fun i => P.allowance x Z (c i) (r i) • Ω) atTop (𝓝 (z • Ω)) :=
    (refreshing Z B.launch B.ready Twah.keyV_go).smul_const _
  have hl := (thin_dew_loss Z B t h).add ht
  rw [zero_add] at hl
  exact hl.congr fun i => (show E (t i) (P.lucid x Z (c i) (r i)) = _ + _ from
    (congrArg (fun y:H => E (t i) y) (P.halo_split ..)).trans ((map_add (E (t i)) _ _).trans
      (congrArg (E (t i) (ϕ i) + ·) ((map_smul (E (t i)) _ Ω).trans
        (congrArg (P.allowance x Z (c i) (r i) • ·) (P.heaven_hot ..)))))).symm

/-- Unprojected estimate. Useful for directly reading grids, simultaneously with
shrinking the physical intrinsic width. -/
lemma thin_front_shard_tendsto (t : ℕ → ℝ≥0)
    (h : Tendsto (fun i => (t i:ℝ)/(ρ i)) atTop atTop) :
    Tendsto (fun i => (R).E (t i) (P.shard x Z (c i) (r i))) atTop (𝓝 (z • ω)) := by
  let X (i:ℕ) := P.shard x Z (c i) (r i)
  let V := P.visitors 3 ξ
  let Y (i:ℕ) := (R).E (t i)
  have he : Tendsto (fun i => Y i (V (X i))) atTop (𝓝 (z • ω)) := by
    have hv : Tendsto (fun i => λ' (E (t i) (P.lucid x Z (c i) (r i)))) atTop (𝓝 (λ' (z • Ω))) :=
      (λ'.continuous.tendsto (z • Ω)).comp (thin_front_lucid_tendsto Z B t h)
    refine hv.congr ?_
    intro i
    exact P.soleHeat 3 ξ (t i) (P.lucid x Z (c i) (r i))
  have hl : Tendsto (fun i => V (X i) - X i) atTop (𝓝 0) :=
    whole_sky (P:=P) (c:=c) (r:=r) (x:=x) Z B.launch B.ready Twah.keyV_go
  have hs : Tendsto (fun i => Y i (V (X i) - X i)) atTop (𝓝 0) :=
    soarL R t _ hl
  have ht : Tendsto (fun i => Y i (V (X i)) - Y i (V (X i) - X i)) atTop (𝓝 (z • ω)) := by
    have hh := he.sub hs
    rw [sub_zero] at hh
    exact hh
  refine ht.congr fun i => ?_
  change Y i (V (X i)) - Y i (V (X i)-X i) = Y i (X i)
  rw [map_sub,sub_sub_cancel]
/-- Also test the actual existing (time-differenced) six-probe recipe itself at these
shrinking widths. It has *no* nonzero total response limit with that normalization;
here is the actor estimate. -/
lemma thin_old_shard_tendsto (t : ℕ → ℝ≥0)
    (h : Tendsto (fun i => (t i:ℝ)/(ρ i)) atTop atTop) :
    Tendsto (fun i => (R).E (t i) (P.filterVector x (c i) (r i) Z)) atTop (𝓝 0) := by
  let d (i : ℕ) := P.increment (c i) (r i)
  have hd : Tendsto (fun i => ((t i + d i:ℝ≥0):ℝ)/(ρ i)) atTop atTop :=
    tendsto_atTop_mono (fun i =>
      div_le_div_of_nonneg_right (show (t i:ℝ) ≤ ↑(t i+d i) from by rw [NNReal.coe_add]; simp)
        (P.dew_pos _ (B.launch.unitSize i)).le) h
  have ht:= (thin_front_shard_tendsto Z B t h).sub (thin_front_shard_tendsto Z B (t+d) hd)
  rw [sub_self] at ht
  refine ht.congr fun i => ?_
  let y := P.shard x Z (c i) (r i)
  exact (show (R).E (t i) (P.filterVector x (c i) (r i) Z) = (R).E (t i) y - (R).E (t i+d i) y from
    (congrArg (fun a:G => (R).E (t i) a) (P.filter_born ..)).trans ((map_sub ((R).E (t i)) y _).trans
      (congrArg ((R).E (t i) y - ·) (DFunLike.congr_fun ((R).time (t i) (d i)).symm y)))).symm

#print axioms thin_front_shard_tendsto
#print axioms thin_old_shard_tendsto
#print axioms thin_dew_loss

end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

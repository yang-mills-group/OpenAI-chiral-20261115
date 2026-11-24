import SatinFixedContrastNovember4
import YM.SU5.Thin.Geometry

/-!
# Cost letting the intrinsic width go to zero, in physical units

Different level purchases of the thin field (first term of the Six probe).
This estimate is on the full, unprojected, selected Euclidean vacuum Hilbert
space, with its `P.colorZero`. It is **strong** convergence in external-slack
readings. Really a width (Cauchy) test; sending the field through the external
Euclidean heat to the seam does not even require selecting a subsequence of
widths beyond the Six `Experiment` election.

This is NOT an internal heat-buffer reinterpretation of a single old finite
stencil. Directly calculate the effect of shrinking these insertions, with their
normalization, on this very character. We find that in the limit only the vacuum
component survives at fixed physical separation. To obtain the upper estimate
use an intermediate *moving* separation (still on this same law). This is where
the internal scale matters. Local reference `the construction notes`, §
"both contact margins, but loss of propagation", suggests this heat squeeze;
here we use the rigorous spectral zoom limits of the included library.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
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
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
section contraction
variable (X:Hilbert) (S:OS.Semigroup X (3:Axis))

lemma heat_minorizes (z:X) {a b:ℝ≥0} (h:a≤b) : ‖S.E b z‖ ≤ ‖S.E a z‖ := by
  nth_rw 1 [← tsub_add_cancel_of_le h,S.time]
  rw [ContinuousLinearMap.comp_apply]
  exact ((S.E (b-a)).le_opNorm _).trans
    (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _))

lemma heat_nonexpanding (t:ℝ≥0) (z z':X) : dist (S.E t z) (S.E t z') ≤ dist z z' := by
  simp_rw [dist_eq_norm, ← map_sub]
  exact ((S.E t).le_opNorm _).trans
    (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _))
end contraction

open Cheer (FLap Narrow Lyrical)
namespace ThinEstimate
variable (X V:Hilbert) (S:OS.Semigroup X (3:Axis)) (S':OS.Semigroup V (3:Axis))

private lemma shore_zero : Cheer.shore 0 = 0 :=
  Subtype.ext (show position (0:Space3) 0=0 from by rw [←Mink.combine_at]; exact map_zero _)

variable (ξ η:ℕ → X) (ω:X) (g:ℕ → ℝ≥0) (μ:Narrow)
variable (w:Lyrical μ (fun n=> Cheer.outlay S (ξ n) (g n)))
include w
lemma zoom (t:ℝ≥0) : Tendsto (fun i:ℕ=> ‖S.E (((g i)*t)/2) (ξ i)‖^2)
    atTop (𝓝 (FLap μ 0 ((t:ℝ):ℂ)).re) := by
  refine (Complex.continuous_re.continuousAt.tendsto.comp (w.meets 0 t)).congr fun i=>?_
  change (Cheer.FLap (Cheer.outlay S (ξ i) (g i)) 0 ((t:ℝ):ℂ)).re = _
  rw [Cheer.back S (ξ i) (g i) t 0, shore_zero, smul_zero]
  change (inner ℂ (ξ i) (S.U 0 (S.E (g i*t) (ξ i)))).re = _
  rw [S.uZero]
  exact re_milk S _ _
lemma squeeze (f:Tendsto (fun t:ℕ=> FLap μ 0 (t:ℂ)) atTop (𝓝 0))
    (v:Tendsto (fun i:ℕ=> (g i:ℝ)) atTop (𝓝 0)) (a:ℝ≥0) (e:0<a) :
    Tendsto (fun i=> S.E a (ξ i)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε p
  have he : 0<ε^2:= sq_pos_of_pos p
  have ht:= Complex.continuous_re.continuousAt.tendsto.comp f
  rw [Complex.zero_re] at ht
  obtain ⟨t,hQ⟩:= (ht.eventually (gt_mem_nhds he)).exists
  change (FLap μ 0 (t:ℂ)).re < ε^2 at hQ
  have hb : Tendsto (fun i => (↑(((g i)*t)/2 : ℝ≥0):ℝ)) atTop (𝓝 0) := by
    push_cast; simpa only [zero_mul,zero_div] using ((v.mul_const (t:ℝ)).div_const 2)
  have hh:= zoom X S ξ g μ w (t : ℝ≥0)
  rw [NNReal.coe_natCast, Complex.ofReal_natCast] at hh
  filter_upwards [hh.eventually (gt_mem_nhds hQ), hb.eventually (gt_mem_nhds
      (show 0 < (a:ℝ) from NNReal.coe_pos.mpr e))] with i h v
  rw [dist_zero_right]
  have ha: (g i*t)/2 ≤ a := NNReal.coe_le_coe.mp v.le
  apply lt_of_le_of_lt (heat_minorizes X S _ ha) ?_
  exact (sq_lt_sq₀ (norm_nonneg _) p.le).mp h
omit w
lemma assemble (c:ℕ→ℂ)(α:ℂ)(a:ℝ≥0)
    (h: Tendsto (fun i=> S.E a (ξ i)) atTop (𝓝 0)) (p:Tendsto c atTop (𝓝 α))
    (v: S.E a ω=ω)(u:∀ i,η i=ξ i+c i • ω) :
    Tendsto (fun i:ℕ=> S.E a (η i)) atTop (𝓝 (α • ω)) := by
  have ht:= h.add (p.smul (tendsto_const_nhds (x:= ω)))
  rw [zero_add] at ht
  exact ht.congr fun i=>by rw [u,map_add,map_smul,v]

lemma beforeProjection (l:X.space →ₗᵢ[ℂ] V.space) (z:X) (f:ℕ→ V) (y:V) (c:ℂ) (a:ℝ≥0)
    (p:Tendsto (fun i=> S.E a (ξ i)) atTop (𝓝 (c • z)))
    (k:Tendsto (fun i=> l (ξ i)-f i) atTop (𝓝 0))
    (u:∀ i,l (S.E a (ξ i))= S'.E a (l (ξ i))) (v:l z=y):
    Tendsto (fun i=> S'.E a (f i)) atTop (𝓝 (c • y)) := by
  have ht:= l.continuous.continuousAt.tendsto.comp p
  have hp:= (S'.E a).continuous.continuousAt.tendsto.comp k
  have hy := ht.sub hp
  rw [map_smul,v,map_zero,sub_zero] at hy
  exact hy.congr fun i=> by dsimp only [Function.comp_apply]; rw [u,map_sub,sub_sub_cancel]

lemma uniform (c:ℂ) (a:ℝ≥0) (ε:ℝ)(h:0<ε)
    (u:Tendsto (fun i=> S.E a (ξ i)) atTop (𝓝 (c • ω))) (v:∀ t,S.E t ω=ω) :
    ∀ᶠ i:ℕ in atTop, ∀ b:ℝ≥0, a ≤ b → dist (S.E b (ξ i)) (c • ω)<ε := by
  filter_upwards [Metric.tendsto_nhds.mp u ε h] with i hi
  intro b hb
  have ht (t:ℝ≥0)(u:X) : dist (S.E t u) (c • ω) = ‖S.E t (u-c • ω)‖ := by
    rw [dist_eq_norm,map_sub,map_smul,v]
  refine lt_of_le_of_lt ?_ (show dist (S.E a (ξ i)) (c • ω) < ε from hi)
  rw [ht,ht]; exact heat_minorizes X S _ hb

lemma losesDamping (c:ℕ→ℂ) (α:ℂ)(p:Tendsto c atTop (𝓝 α))
    (b:∀ i,η i = ξ i + c i • ω)(f:0 < (FLap μ 0 0).re)
    (θ:ℕ→V)(ω':V)(l:V.space→L[ℂ] X.space)(u:l ω'=ω)(k:l∘θ=η)
    (w:Lyrical μ (fun n=> Cheer.outlay S (ξ n) (g n))) :
    ¬ Tendsto θ atTop (𝓝 (α • ω')) := by
  intro h
  have q:= zoom X S ξ g μ w 0
  have v:= l.continuous.continuousAt.tendsto.comp h
  rw [k,map_smul,u] at v
  have hp:= (v.sub (p.smul (tendsto_const_nhds (x:= ω)))).norm.pow 2
  simp_rw [b,add_sub_cancel_right,sub_self,norm_zero,zero_pow (by decide : (2:ℕ)≠0)] at hp
  simp_rw [mul_zero,zero_div,S.eZero,ContinuousLinearMap.id_apply,NNReal.coe_zero,Complex.ofReal_zero] at q
  exact f.ne' (tendsto_nhds_unique q hp)
end ThinEstimate

section thinning
variable (P:Spine) (x:P.Spectrum0 3) (Z:Lead.Clan) (s n:ℕ)
local notation "ξ" => P.otherSpectrum 3 3 x -- use the adjustment even here
local notation "H'" => P.ColorHil 3 (P.otherSpectrum 3 3 x)
local notation "H" => P.ManyF 3 (P.otherSpectrum 3 3 x)
local notation "E'" => (P.physicalEnergy 3 ξ).E
local notation "ν" => P.seasons 3 ξ
local notation "E" => (P.seasons 3 ξ).E
local notation "ω" => P.colorZero 3 ξ
local notation "Ω" => P.heaven 3 ξ
local notation "G" => P.shard x Z
local notation "Y" => P.lucid x Z
local notation "γ" => (↑(purePrice Z) : ℂ)
local notation "ϕ" => P.birthCloud x Z

lemma string_identity : P.viewF 3 ξ s (P.thinString_birth Z s n)=G s n := rfl
lemma string_mean : P.singleState 3 s x (P.thinString Z s n).F = P.allowance x Z s n :=
  (P.single_agrees 3 3 x s _).symm

open Cheer (Narrow FLap Lyrical)
-- kill the last possible zero-energy part of the price: the spectral zoom measure
-- isn't supported at zero. In fact it's (proved in the library) concentrated in
-- the OPEN positive-energy region. Thus its big-Laplace-point mass vanishes.
lemma thin_decay : Tendsto (fun t:ℕ=> FLap (promenade Z) 0 (t:ℂ)) atTop (𝓝 0) := by
  let μ : Measure E4 := (promenade Z : Measure E4)
  let f (t:ℕ) := Cheer.tendsK 0 (t:ℂ)
  haveI : IsFiniteMeasure μ := (promenade Z).property
  have ha (t:ℕ) (w:E4) : f t w = ((Real.exp (-((t:ℝ)*time w)) : ℝ) : ℂ) := by
    unfold f Cheer.tendsK
    push_cast
    simp
  have he : ∀ᵐ x∂μ, 0<time x := (promenade_strict Z).mono fun p h=> ((Mink.strict_self _).1 h).1
  have ht : Tendsto (fun t:ℕ=> ∫ w,f t w ∂ μ) atTop (𝓝 (∫ _:E4,(0:ℂ) ∂ μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _=> (1:ℝ))
      (fun t => (Cheer.destined (promenade Z) _ _ (home_bright Z) (show 0 ≤ (t:ℂ).re by simp)).1)
      (integrable_const _)
    · intro t
      exact he.mono fun w p => Cheer.withinK _ _ _ (by simp) p.le
    filter_upwards [he] with w hw
    have hr : Tendsto (fun t:ℕ=> (t:ℝ) * time w) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const hw
    have hp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hr
    change Tendsto (fun t:ℕ => f t w) _ _
    simpa only [ha, Function.comp_def, Complex.ofReal_zero] using
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hp)
  rw [integral_zero] at ht
  exact ht

variable {P x} {c r:ℕ→ℕ} {K:P.Register} {J:P.Ellis 3 x} (R:P.Experiment K c r x J)
local notation "δ" i:max=> dewN R.launch i

include R
/-- An intermediate separation, shrinking in physical units (but allowing any
fixed ratio to the `dew` scale of these n along these widths). Controls even the
centered spectral price there. -/
lemma thin_hot_zoom (t:ℝ≥0) : Tendsto (fun i:ℕ=> ‖E (((δ i)*t)/2) (ϕ (c i) (r i))‖^2)
    atTop (𝓝 (FLap (promenade Z) 0 ((t:ℝ):ℂ)).re) :=
  ThinEstimate.zoom (H) (ν) (fun i=>ϕ (c i) (r i)) (dewN R.launch) _
    (lyricalCloud Z R.launch R.ready Twah.keyV_go (R.ground.2.1.accepted 3)) t

lemma thin_projected_cost (a:ℝ≥0) (e:0<a) :
    Tendsto (fun i=> E a (ϕ (c i) (r i))) atTop (𝓝 0) :=
  ThinEstimate.squeeze (H) (ν) (fun i=>ϕ (c i) (r i)) (dewN R.launch) _
    (lyricalCloud Z R.launch R.ready Twah.keyV_go (R.ground.2.1.accepted 3))
    (thin_decay Z) (P.proper_dew c r R.launch) a e

/-- With the normalized price of this string, the smearable field on the vacuum
has a particularly strong limiting law in the *projected* physical Hilbert space. -/
lemma thin_projected (a:ℝ≥0) (p:0<a) :
    Tendsto (fun i:ℕ=> E a (Y (c i) (r i))) atTop (𝓝 (γ • Ω)) :=
  ThinEstimate.assemble (H) (ν) _ _ (Ω) _ _ a (thin_projected_cost Z R a p)
    (refreshing Z R.launch R.ready Twah.keyV_go) (P.heaven_hot ..) (fun i=> P.halo_split x Z (c i) (r i))

/-- No spatial projection cheat to claim a field limit. Even before projecting,
every purchase with positive external clearance in the time coordinate suffices,
at the true positions on the physical mesh. This estimate works for fixed-small
slack (conclusions only after width removal, not uniform down to no time separation).
`S.ℚmeasure` of a cone model is NOT assumed. -/
lemma thin_cost (a:ℝ≥0) (e:0<a) : Tendsto (fun i=> E' a (G (c i) (r i))) atTop
    (𝓝 (γ • ω)) :=
  ThinEstimate.beforeProjection (H) (H') (ν) (P.physicalEnergy 3 ξ)
    _ (P.enter 3 ξ) Ω (fun i=> G (c i) (r i)) ω γ a
    (thin_projected Z R a e)
    (whole_sky Z R.launch R.ready Twah.keyV_go)
    (fun _i=> rfl) rfl

/-- Arbitrary larger exposure as well. -/
lemma thin_uniform_heat (a:ℝ≥0) (e:0<a) (ε:ℝ)(h:0<ε) :
    ∀ᶠ i:ℕ in atTop, ∀ b:ℝ≥0, a ≤ b → dist (E' b (G (c i) (r i))) (γ • ω)<ε :=
  ThinEstimate.uniform (H') (P.physicalEnergy 3 ξ) _ ω γ a ε h
    (thin_cost Z R a e) (P.sector_hot 3 ξ)

-- carry/investigate the obstruction test even for this vacuum vector.
-- Can't claim this convergence *uniform* removing external time separation:
-- unsmeared undamped vector still has POSITIVE outlay off the vacuum line.
omit R
lemma thin_zerotime_positive : 0 < (Cheer.FLap (promenade Z) 0 0).re := by
  rw [Cheer.launched_z]
  change 0 < ((promenade Z).mass:ℝ)
  apply NNReal.coe_pos.mpr
  have h:= Measure.measure_univ_pos.mpr (promenade_ne Z)
  rw [← FiniteMeasure.ennreal_mass] at h
  exact_mod_cast h

include R
lemma thin_damping_needed : ¬ Tendsto (fun i=> G (c i) (r i)) atTop (𝓝 (γ • ω)) :=
  ThinEstimate.losesDamping (H) (H') (ν) (fun i=>ϕ (c i) (r i)) (fun i=> Y (c i) (r i)) Ω
    (dewN R.launch) _ (fun i=>P.allowance x Z (c i) (r i)) γ
    (refreshing Z R.launch R.ready Twah.keyV_go) (fun i=> P.halo_split x Z (c i) (r i)) (thin_zerotime_positive Z)
    _ ω (P.wealth 3 ξ) (P.stone_mark 3 ξ) rfl
    (lyricalCloud Z R.launch R.ready Twah.keyV_go (R.ground.2.1.accepted 3))

#print axioms thin_decay
#print axioms thin_hot_zoom
#print axioms thin_uniform_heat
#print axioms thin_damping_needed
end thinning
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

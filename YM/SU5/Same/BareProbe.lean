import YM.SU5.Same.Lab

/-!
# Analytic assessment of identifying the comparator

Construct a check on one of the needed estimates. Turns out can pay the
(six-family, strict positivity, vanishing one-point, and arbitrarily strictly positive heat field costs)
with **only pure gauge** probes giving the **same** limiting KET fields and
thus the very Gram answers. Approximation necessary also after the time-jet
operations.

This doesn't overturn the actual genuine mixed stencil registration at CP18;
rather addresses how to interpret its raw comparator against the physical
sector questions. Presentations matter. No continuity/descent of the comparator
with respect to replacing with stencils implementing exactly the same Eu
realization presently constructed (width-limit norm on applied-to-vacuum, or
the heated profiles). Cannot invoke a physical decoupled prediction depending
only on these KET data, compatible with these presentations, to obtain the desired
interaction.

Not ruling out *operator*-sensitive tests. In fact, even coincidence on those
operators would not rule out the very different coupling-comparison questions
which continue those compounds to decoupled predictions via the same Mark recipe,
without asking them to descend to the quotient by those operators (e.g. if the two
theories have different equation/field identifications). So this diagnostic isn't
a denial of specific interaction interpretations; nor claiming detection in them.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 4000
set_option maxHeartbeats 500000
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
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets

variable (P : Spine)
local notation "K" => P.calibration
local notation "θ₀" => (3:Axis)

section single
variable (a : Lead.Clan) (B : P.Apron) (s n : ℕ)
local notation "Φ" i:max => P.shifts θ₀ i
local notation "A" => P.stitchApron a B s n
local notation "δ" => B.zoom P s θ₀
local notation "G" => (Φ (δ:ℤ)) (B.full P s)
local notation "p₀" => (purePrice a:ℂ)

/-- Keep **whole** budget and scheduling; don't insert any matter, replace
that front channel by precisely the scalar used in the sewn operator estimate. -/
def gaugeStitch : P.Apron :=
  { A with
    F := (purePrice a:ℂ) • ((P.shifts θ₀ (B.zoom P s θ₀)) (B.full P s))
    bay := ((bay K ((A).S) true).smul_mem ((tallerBay _ _ _ subset_union_left)
      (P.shifts_support θ₀ _ _ ((Tower.proceeds P.run P.large P.history.circuit B.s (s-B.s)
        ((Tapestry.locates ..).1 B.bay)).1))) _)
    realM := Subalgebra.smul_mem _ (P.shifts_keep θ₀ _ (B.fullColor P s)) _ }
local notation "A'" => P.gaugeStitch a B s n

lemma gaugeStitch_pure (h : PureGauge K B.F) : PureGauge K (A').F :=
  (gaugePlane K).smul_mem (purePrice a:ℂ) (P.shifts_pure _ θ₀ _ (P.convey_pure B.s B.F h (s-B.s)))
lemma front_bookGauge (h : B.s ≤ s) (x : P.Spectrum0 3) :
    ∃ p : P.birthF 3 s ((A').F), P.viewF 3 x s p = (purePrice a:ℂ) • (B.engine P 3 x) (P.colorZero 3 x) := by
  obtain ⟨p,hp⟩ := B.overnight P θ₀ x s h (P.faceUnit θ₀ s)
  have hx : G * P.shifts θ₀ ((δ:ℕ)+(δ:ℕ)) 1 = G := by rw [map_one,mul_one]
  let p' : P.birthF θ₀ s G := hx ▸ p
  refine ⟨P.birthScaleJ θ₀ s p₀ p',(P.viewJ_scale θ₀ x s p₀ p').trans (congrArg (p₀ • ·) ?_)⟩
  exact (P.identical_F θ₀ x s p' p hx.symm).trans (hp.trans (congrArg (B.engine P θ₀ x) (P.view_one θ₀ x s)))
end single

section gauge

lemma reflect_keepsPure {s : P.Test} (h : PureGauge K s) (j : Axis) : PureGauge K (P.reflectTest j s) :=
  (P.pale_iff _).mp (mirror_pale K s.val (pure_pale K h) j 0)
lemma kept_pure_field {s : ℕ} (F : P.Test) (h : PureGauge K F) (k : ℕ) : PureGauge K (P.tubaField s F k) := by
  induction k with
  | zero => exact h
  | succ n ih =>
    rw [tubaField]
    exact (gaugePlane K).smul_mem _ ((gaugePlane K).sub_mem (P.shifts_pure _ _ _ ih) ih)
lemma kept_pure (B : P.Apron) (w : Prism) (h : PureGauge K B.F) : PureGauge K (P.aTuba w B).F :=
  P.shifts_pure _ _ _ ((gaugePlane K).sum_mem fun i _ => (gaugePlane K).smul_mem (w i) (P.kept_pure_field (s:=B.s) B.F h (i+1)))
lemma survey_pure (F : P.Test) (h : PureGauge K F) (L : List Axis) (z : Cover) :
    PureGauge K ((P.cruise L z) F) := by
  induction L with
  | nil => exact h
  | cons i l ih =>
    rw [P.cruise_step,AlgHom.comp_apply]; exact P.shifts_pure _ _ _ ih
lemma issue_pure (B : P.Apron) (t : ℕ) (h : PureGauge K B.F) (i : Cover) : PureGauge K (P.issuing t B i) :=
  P.survey_pure _ (P.convey_pure B.s B.F h (t-B.s)) Vacancy.ordinate _
lemma prepare_pure (B : P.Apron) (t : ℕ) (h : PureGauge K B.F) (F : SampleDose) :
    PureGauge K (P.prepared t B F) :=
  (gaugePlane K).sum_mem fun i _ => (gaugePlane K).smul_mem _ (P.issue_pure B t h i)
end gauge

variable (x:P.Spectrum0 3) (A:ℕ→P.Apron) (c r n:ℕ→ℕ)
variable (w : Lead.Clan → Prism) (T' : P.HandleWith x c r A n)
local notation "ξ" => P.advocate 3 x 3
local notation "H" => P.ColorHil 3 (P.advocate 3 x 3)
local notation "Hc" => P.ManyF 3 (P.advocate 3 x 3)
local notation "E" => P.physicalEnergy 3 (P.advocate 3 x 3)
local notation "E'" => P.seasons 3 (P.advocate 3 x 3)
local notation "m!" i:max => c (n i)

abbrev gaugeTrumpet (a : Lead.Clan) (i : ℕ) : P.Apron := P.aTuba (w a) (P.gaugeStitch a (A i) (c (n i)) (r (n i)))
local notation "Q" k:max i:max => P.soldTrumpet A c r n w k i
local notation "B" k:max i:max => P.stitchApron k (A i) (c (n i)) (r (n i))
local notation "G" k:max i:max => P.gaugeTrumpet A c r n w k i
local notation "Z" k:max i:max => P.gaugeStitch k (A i) (c (n i)) (r (n i))
variable (a : Lead.Clan)

include T' in
lemma gauge_birth (i : ℕ) : P.birthF 3 (m! i) (Z a i).F := (P.front_bookGauge a _ _ _ (T'.already i) x).choose
local notation "δ" i:max => P.gauge_birth x A c r n T' a i
lemma gaugeTrumpet_purity (i : ℕ) (h : PureGauge K (A i).F) : PureGauge K (G a i).F :=
  P.kept_pure _ _ (P.gaugeStitch_pure a (A i) (c (n i)) (r (n i)) h)
include T' in
lemma gaugeTrumpet_birth (i : ℕ) : P.birthF 3 (m! i) ((G a i).F) := P.plays_birth (w a) (Z a i) (δ i)
lemma gaugeTrumpet_width (i : ℕ) (j : Axis) : (G a i).realWidth P j = (Q a i).realWidth P j := by simp only [gaugeTrumpet,soldTrumpet,P.tuba_width]; rfl

local notation "γ" i:max => P.stitch_clear a x c r A n T' i
local notation "q₀" i:max => P.gaugeTrumpet_birth x A c r n w T' a i
local notation "q'" i:max => P.sold_birth x A c r n w a i T'
lemma currencies (i : ℕ) : ‖P.viewF 3 ξ (m! i) (γ i) - P.viewF 3 ξ (m! i) (δ i)‖ ≤ P.macroStep i := by
  have he := (P.stitch_certificate a (r (n i)) x (T'.already i)).choose_spec
  rw [he,(P.front_bookGauge a _ _ _ (T'.already i) ξ).choose_spec]
  exact T'.price i a

lemma heated_distance (i : ℕ) (t : ℝ) : dist (P.cradleH x (B a i) (γ i) t) (P.cradleH x (Z a i) (δ i) t) ≤ P.macroStep i := by
  let X := P.viewF 3 ξ (m! i) (γ i)
  let Y := P.viewF 3 ξ (m! i) (δ i)
  let S := (E).E t.toNNReal
  change dist (S X) (S Y) ≤ _
  rw [dist_eq_norm, ← map_sub]
  exact ((S.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) ((E).shrinks _))).trans
    (P.currencies x A c r n T' a i)

variable (V : ∀ j:Axis,List Axis → ℝ → P.ColorHil j (P.advocate 3 x j)) (g h : ℕ)
variable (D : P.ThinArmada x A c r n w T' V g h)
include D
lemma gauge_profile_H (t : ℝ) (p : 0 < t) : Tendsto (fun i => P.cradleH x (Z a i) (δ i) t)
    atTop (𝓝 (P.route_before a x V t)) := by
  refine ((D.fusion.receipt a).1.1 _ p).congr_dist ?_
  exact squeeze_zero (fun i=> dist_nonneg) (fun i=> P.heated_distance x A c r n T' a i t) P.macroStep_zero

omit D in
private lemma shadowHeated (L:Hilbert)(H₀:OS.Semigroup L 3)(Vx:Prism)(e:ℕ→ℝ≥0)(p:Tendsto e atTop (𝓝 0))(g:∀ i,0<e i)(f:ℝ→L)(A:ℕ→ℝ→L)(h:Positive H₀ f)
    (W:Operates (f:=atTop) H₀ f A)(t:ℝ)(τ:0<t): Tendsto (fun i=>H₀.E (e i) (prism_on H₀ Vx (e i) (A i t))) atTop (𝓝 (prism H₀ f Vx t)):= by
 let y:= prism H₀ f Vx t
 have hp:Tendsto (fun i=>H₀.E (e i) (prism_on H₀ Vx (e i) (A i t))) atTop (𝓝 (H₀.E 0 y)):=
    ((heat_both L 3 H₀).tendsto _).comp (p.prodMk_nhds (prism_limit H₀ f Vx h A W p (Eventually.of_forall g) τ))
 rw [H₀.eZero, ContinuousLinearMap.id_apply] at hp; exact hp
/-- Handoff to the same stencil's final derivative operations, only with each `t>0`
heat paid. No estimates from this uniform as t goes to zero. -/
lemma gaugeTrumpet_heat_H (t : ℝ) (p : 0 < t) :
    Tendsto (fun i => P.cradleH x (G a i) (q₀ i) t) atTop (𝓝 (P.profilesH x w a V t)) := by
  let e(i:ℕ) := P.burst (m! i)
  have ht : Tendsto e atTop (𝓝 0) := P.burst_zero.comp D.fusion.high.tendsto_atTop
  have hu(i) : 0 < e i := P.burst_p _
  -- same calculus as `heatedCash` used to certify CP18.
  let y := P.profilesH x w a V t
  let L := P.operates_from x (fun i => Z a i) (P.route_before a x V) (fun i => δ i)
    (P.gauge_profile_H x A c r n w T' a V g h D)
  have hp := shadowHeated H E (w a) e ht hu (P.route_before a x V)
    (fun i => P.cradleH x (Z a i) (δ i)) (D.fusion.profile a) L.1 t p
  refine hp.congr fun i=> ?_
  have eq (i : ℕ) : P.burst ((Z a i).s) = e i := rfl
  have he := P.tuba_quenches x (Z a i) (w a) (δ i) t
  rw [eq] at he; exact he.symm
lemma gaugeTrumpet_heat_G (t : ℝ) (p : 0 < t) :
    Tendsto (fun i => P.cradleG x (G a i) (q₀ i) t) atTop (𝓝 (P.profilesZ x V w a t)) := by
  simp_rw [P.cradle_bank,←P.illuminate_bank x A c r n w V g h T' D a t p]
  exact ((P.wealth 3 ξ).continuous.tendsto _).comp (P.gaugeTrumpet_heat_H x A c r n w T' a V g h D t p)

#print axioms gaugeTrumpet_heat_H
#print axioms gaugeTrumpet_heat_G
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

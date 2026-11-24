-- Under SU5SatinVerifiedNovember6 in final integration
import SatinProbeCompatibilityNovember6

/-!
# On the CP18 stencil comparison: the pure-clover twin problem

This file does NOT use `boost` or positive-heat Mink locality assumptions. We compute in the
*given unshrunk* system and its existing Euclidean thin kernel. Which comparisons on the
proposed local fields can be intrinsic in terms of those data?

This rules out getting the comparator on that field data by descent under what CP18 proves about
fields so far (vacuum vector equivalence, including *arbitrary* positive imaginary times here).
Doesn't rule out proving interpretations based on more structure. Doesn't assert existence of
local operators! Details in the checkpoint.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4000
set_option maxHeartbeats 350000
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
open MacroGrid SatinNucleus SatinJets DoseTravel Set

variable (P : Spine) (x : P.Spectrum0 3)
local notation "ξ" => P.advocate 3 x 3
local notation "H" => P.ColorHil 3 ξ
local notation "G" => P.ManyF 3 ξ
local notation "κ" => P.calibration
local notation "S" => P.physicalEnergy 3 ξ
local notation "S'" => P.seasons 3 ξ
local notation "T" => timeMesh P.par
local notation "E" k => P.singleState 3 k x

section aux
variable (B : P.Apron) (J : Prism)
lemma realWidth_ge_step (j : Axis) : P.macroStep B.s ≤ B.realWidth P j := by
  change (mill T B.s:ℝ) ≤ (↑(↑(B.u j):ℤ):ℝ) * _
  apply le_mul_of_one_le_left (le_of_lt (P.macroStep_pos _))
  exact_mod_cast B.pos j

lemma height_of_width (D : ℕ → P.Apron) (j : Axis)
    (h : Tendsto (fun i => (D i).realWidth P j) atTop (𝓝 0)) :
    Tendsto (fun i => (D i).s) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro k
  filter_upwards [h.eventually (gt_mem_nhds (P.macroStep_pos k))] with i hv
  change (D i).realWidth P j < P.macroStep k at hv
  change k ≤ (D i).s
  by_contra! hk
  have ha : P.macroStep k ≤ P.macroStep (D i).s := by
    suffices mill (timeMesh P.par) k ≤ mill (timeMesh P.par) (D i).s from this
    rw [← mill_finer T (D i).s k hk.le]
    refine le_mul_of_one_le_left (mill_pos ..|>.le) ?_
    apply one_le_pow₀
    exact_mod_cast Nat.le_trans (show 1 ≤ 2 by decide) (T).Llarge
  exact (not_lt_of_ge (ha.trans (P.realWidth_ge_step (D i) j))) hv

/-- All strict time pads on the final ColorHil. -/
lemma cash_birth_points (D : ℕ → P.Apron) {Y : ∀ j:Axis, List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)}
    (p : Radiates P x D Y) (q : ∀ i, P.birthF 3 (D i).s (D i).F) (t : ℝ) (e : 0<t) :
    Tendsto (fun i => P.cradleH x (D i) (q i) t) atTop (𝓝 (Y 3 [] t)) := by
  refine (p.cash 3 [] t e).congr' ?_
  filter_upwards [(p.slender 3).eventually (gt_mem_nhds e)] with i h
  let w := (D i).realWidth P 3
  have hv : w < t := h
  have hw : 0 ≤ w := ((D i).real_width_pos P 3).le
  change (S).E (t-w).toNNReal ((D i).engine P 3 ξ (P.colorZero 3 ξ)) = _
  rw [P.thinRawEntry x (D i) (q i), ← ContinuousLinearMap.comp_apply, ← OS.Semigroup.time]
  have hu : (t-w).toNNReal+w.toNNReal=t.toNNReal := by
    apply NNReal.eq
    rw [NNReal.coe_add, Real.coe_toNNReal _ (sub_nonneg.mpr hv.le),
      Real.coe_toNNReal _ hw, Real.coe_toNNReal _ e.le]
    exact sub_add_cancel ..
  change (S).E ((t-w).toNNReal+w.toNNReal) _ = _
  rw [hu]

/-- Scaling of the gauge base by the very same constant. -/
def pricedTwinBase (B : P.Apron) (a : Lead.Clan) : P.Apron where
  s := B.s
  «S» := B.S
  u := B.u
  F := (purePrice a : ℂ) • B.F
  pos := B.pos
  shelter := B.shelter
  bay := (bay κ B.S true).smul_mem B.bay _
  realM := (enclave κ).smul_mem B.realM _

lemma pureTwin_tuba (h : PureGauge κ B.F) : PureGauge κ (P.aTuba J B).F := by
  apply shifts_pure
  change P.drumroll B.s B.F J ∈ gaugePlane κ
  refine Submodule.sum_mem (gaugePlane κ) ?_
  intro i t
  apply Submodule.smul_mem
  suffices ∀ n:ℕ, P.tubaField B.s B.F n ∈ gaugePlane κ from this _
  intro n
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [tubaField]
    refine Submodule.smul_mem _ _ ((gaugePlane κ).sub_mem (P.shifts_pure _ _ _ ih) ih)

lemma pureTwin_mul (a b : P.Test) (ha : PureGauge κ a) (hb : PureGauge κ b) :
    PureGauge κ (a*b) := by
  apply (P.pale_iff (a*b)).1
  intro n x
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.1 ((P.pale_iff _).2 ha n x)
  obtain ⟨d,hd⟩ := Submodule.mem_span_singleton.1 ((P.pale_iff _).2 hb n x)
  apply Submodule.mem_span_singleton.2
  change ∃ z:ℂ, z • (1 : FC (Single (P.calibration.c n))) = a.val n x * b.val n x
  rw [← hc, ← hd]
  refine ⟨c*d,?_⟩
  rw [mul_smul, Algebra.smul_mul_assoc, one_mul]

lemma pureTwin_kiss (h : PureGauge κ B.F) (j : Axis) : PureGauge κ (B.kiss P j).F :=
  (P.pale_iff _).1 (Six.mirror_pale _ _ ((P.pale_iff _).2 h) _ _)

lemma pureTwin_cruise (A : P.Test) (p : PureGauge κ A) (o : Cover) (L : List Axis) :
    PureGauge κ (P.cruise L o A) := by
  induction L with
  | nil => exact p
  | cons j l h => exact P.shifts_pure (P.cruise l o A) j (o j) h

lemma pureTwin_issue (p : PureGauge κ B.F) (k : ℕ) (o : Cover) :
    PureGauge κ (P.issuing k B o) :=
  P.pureTwin_cruise _ (P.convey_pure B.s _ p (k-B.s)) o _

lemma pureTwin_smear (p : PureGauge κ B.F) (t : ℕ) (F : SampleDose) :
    PureGauge κ (P.prepared t B F) := by
  change P.prepared t B F ∈ gaugePlane κ
  apply Submodule.sum_mem
  intro i h
  apply Submodule.smul_mem
  exact P.pureTwin_issue _ p _ i
end aux

section
variable (A : ℕ → P.Apron) (c r n : ℕ→ℕ) (w : Lead.Clan→ Prism)
variable (V : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j))
variable (g h : ℕ) (X : P.HandleWith x c r A n)

/-- Probe base of the unconditional disclosed experiment in its presentation using `cinema`.
Pay at the scalar from the *same* fusion estimate. For each family keep the same time
differential prescription. -/
noncomputable def bareTwin (a : Lead.Clan) (i : ℕ) : P.Apron :=
  P.aTuba (w a) (P.pricedTwinBase (A i) a)
local notation "B" => P.bareTwin A w
local notation "BP" i:max a:max => P.pricedTwinBase (A i) a

lemma pureTwin_pure (pc : ∀ i, PureGauge κ (A i).F) (a : Lead.Clan) (i : ℕ) :
    PureGauge κ (B a i).F :=
  P.pureTwin_tuba (BP i a) (w a) ((gaugePlane κ).smul_mem _ (pc _))

variable (D : P.ThinArmada x A c r n w X V g h)
include D
lemma bareTwinBase_birth (a : Lead.Clan) (i : ℕ) : P.birthF 3 (A i).s (BP i a).F :=
  P.birthScaleJ 3 (A i).s (purePrice a : ℂ) (D.cinema.resident i)

local notation "BP'" i:max a:max => P.bareTwinBase_birth x A c r n w V g h X D a i
lemma bareTwin_birth (a : Lead.Clan) (i : ℕ) : P.birthF 3 (B a i).s (B a i).F :=
  P.plays_birth (w a) (BP i a) (BP' i a)
local notation "B'" a:max i:max => P.bareTwin_birth x A c r n w V g h X D a i
local notation "Sold" => P.soldTrumpet A c r n w
local notation "s'" a:max i:max => P.sold_birth x A c r n w a i X

lemma bareTwin_height (a : Lead.Clan) : Tendsto (fun i => (B a i).s) atTop atTop :=
  P.height_of_width A 3 (D.cinema.heat.slender 3)

lemma bareTwin_slender (a : Lead.Clan) : P.thicknessZero (B a) := by
  intro j
  have t := P.bareTwin_height x A c r n w V g h X D a
  have k := (D.cinema.heat.slender j).add ((P.macroStep_zero.comp t).const_mul
    (↑(lastTuba (w a) + 1):ℝ))
  rw [mul_zero, zero_add] at k
  exact k.congr (fun i => (P.tuba_width _ _ j).symm)

lemma bareTwin_base_points (a : Lead.Clan) (t : ℝ) (p : 0<t) :
    Tendsto (fun i => P.cradleH x (BP i a) (BP' i a) t) atTop (𝓝 (P.route_before a x V t)) := by
  have q := P.cash_birth_points x A D.cinema.heat D.cinema.resident t p
  refine (q.const_smul (purePrice a:ℂ)).congr ?_
  intro i
  unfold cradleH thinOrigin
  have ht := P.viewJ_scale 3 ξ (A i).s (purePrice a:ℂ) (D.cinema.resident i)
  exact ((congrArg ((S).E t.toNNReal) ht).trans (map_smul _ _ _)).symm

omit D
private lemma cover_price (L:Hilbert) (R:OS.Semigroup L 3) (W:Prism) (f:ℝ→L) (u:Positive R f)
    (M:ℕ→ℝ→L) (v:Operates (f:=atTop) R f M) (e:ℕ→ℝ≥0) (p:Tendsto e atTop (𝓝 0))
    (t:ℝ) (g:∀ i,0<e i) (q:0<t) :
    Tendsto (fun i=>R.E (e i) (prism_on R W (e i) (M i t))) atTop (𝓝 (prism R f W t)) := by
  have l := ((heat_both L 3 R).tendsto (0,prism R f W t)).comp
    (p.prodMk_nhds (prism_limit R f W u M v p (Eventually.of_forall g) q))
  change Tendsto _ _ (𝓝 (R.E 0 (prism R f W t))) at l
  rw [R.eZero, ContinuousLinearMap.id_apply] at l
  exact l

local notation "λ'" => P.enter 3 ξ
local notation "π'" => P.wealth 3 ξ
local notation "Θ" a:max => P.profilesH x w a V
local notation "ΠR" a:max => P.profilesZ x V w a

include D
lemma bareTwin_heated (a : Lead.Clan) (t : ℝ) (p : 0<t) :
    Tendsto (fun i => P.cradleH x (B a i) (B' a i) t) atTop (𝓝 ((Θ a) t)) ∧
    Tendsto (fun i => P.cradleG x (B a i) (B' a i) t) atTop (𝓝 ((ΠR a) t)) := by
  have qa := (P.operates_from x (fun i=> BP i a) _ (fun i=> BP' i a)
    (P.bareTwin_base_points x A c r n w V g h X D a)).1
  have k := (P.burst_zero.comp (P.bareTwin_height x A c r n w V g h X D a))
  have tH : Tendsto (fun i => P.cradleH x (B a i) (B' a i) t) atTop (𝓝 ((Θ a) t)) :=
    (cover_price H (S) (w a) (P.route_before a x V) (D.fusion.profile a) _ qa _ k t
      (fun i=> P.burst_p (A i).s) p).congr (fun i=> (P.tuba_quenches x (BP i a) (w a) _ t).symm)
  refine ⟨tH,?_⟩
  rw [← P.illuminate_bank x A c r n w V g h X D a t p]
  exact (((π').continuous.tendsto _).comp tH).congr (fun _=> (P.cradle_bank x ..).symm)

variable (F U : SampleDose) (J : P.Ellis 3 x)
local notation "R₁" μ:max a:max => DoseTravel.beam G F (P.earlierProfile x V w μ a)
local notation "R₂" μ:max a:max => DoseTravel.beam G U (P.laterProfile x V w μ a)

include J
lemma bareTwin_test (a : Lead.Clan) (μ:ℝ)(u:0<μ)(q:forwardSite U μ):
    Tendsto (fun i=> P.thinKet x (B a i) (B' a i) U) atTop (𝓝 (R₂ μ a)) ∧
    ∀ t:ℕ→ℕ,Tendsto t atTop atTop→ Tendsto (fun i=> P.thinGridKet x (t i) (B a i) (B' a i) U)
      atTop (𝓝 (λ' (R₂ μ a))) := by
  exact ⟨P.dynamic_cont_ket x _ _ _ _ _ _ J (D.energy a).1 u (fun t=> P.illuminate_bank x A c r n w V g h X D a t) q (P.bareTwin_heated x A c r n w V g h X D a μ u).1,
    P.dynamic_grid_ket x _ _ _ _ _ _ J (D.energy a).1 u (fun t=> P.illuminate_bank x A c r n w V g h X D a t) q (P.bareTwin_heated x A c r n w V g h X D a μ u).1⟩

lemma same_thin_vacuum_profile (a : Lead.Clan) (μ:ℝ)(u:0<μ)(q:forwardSite U μ) :
    Tendsto (fun i => P.thinKet x (Sold a i) (s' a i) U - P.thinKet x (B a i) (B' a i) U)
      atTop (𝓝 0) ∧ ∀ t:ℕ→ℕ,Tendsto t atTop atTop → Tendsto (fun i=>
        P.thinGridKet x (t i) (Sold a i) (s' a i) U - P.thinGridKet x (t i) (B a i) (B' a i) U)
      atTop (𝓝 0) := by
  let d₁ := P.illuminate_forward x A c r n w V g h X D J μ a U u q
  let d₂ := P.bareTwin_test x A c r n w V g h X D U J a μ u q
  refine ⟨?_, fun t p => ?_⟩
  · simpa only [sub_self] using d₁.1.sub d₂.1
  simpa only [sub_self] using (d₁.2 t p).sub (d₂.2 t p)
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

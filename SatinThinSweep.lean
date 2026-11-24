import SatinFixedContrastNovember4

import SatinThinWall

/-!
# A thin bilocal-composite experiment: III. Strong limit of the smeared fields on the vacuum

Prove even a *simultaneous* intrinsic-width/fine-grid result. All costs on the
actual elected `ColorHil`, for the forward representatives of the two probes.
This does not assert simultaneous changing of the election cutoff/volume
parameters with the marks. Here these are the **selected-state** vectors and
readings (after the election and normalization). See `Experiment` and
`macroscopicSatin` for the data used in applying it. Also preserve the
specified readings taking first the grid limit (as in II), then width.
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

open MacroGrid Set

section mass
variable (P : Spine) (F : SampleDose)

private lemma thin_integrate_grid (f:Vantage→ℝ)(s:Continuous f)
    (p:Function.support f ⊆ tsupport F.val):
    Tendsto (fun t => ∑ i ∈ P.usedGrid t F,
        P.macroStep t^4 * f (P.meshPose t i)) atTop (𝓝 (∫ x, f x)) := by
  have e: HasCompactSupport f := F.budget.of_isClosed_subset (show IsClosed (tsupport f) from isClosed_closure)
    (closure_minimal p isClosed_closure)
  refine (MacroGrid.rSum_limit P.macroStep P.macroStep_zero f s P.macroStep_pos e).congr fun t=>?_
  let A:= P.usedGrid t F; let d:=P.macroStep t; let g:=f ∘ P.meshPose t
  have he (i:Cover)(w:i∉ A): g i=0:= by
    by_contra q
    exact w ((P.usedPose t F i).2 (p q))
  have h := (room_price d (P.macroStep_pos t) g A he).2
  change (∫ x, floorCost d g x)=∑ i∈ A,d^4 *g i
  simpa only [show Fintype.card Axis=4 from rfl, smul_eq_mul,Finset.mul_sum] using h

/-- Total *signed* weight (thus works also for tests which aren't normalizations). -/
lemma thin_activation_mass : Tendsto (fun t => ∑ i∈ P.usedGrid t F, P.activation t F i)
    atTop (𝓝 ((∫ x, F.val x : ℝ) : ℂ)) := by
  have he: Tendsto (fun t => ((∑ i∈ P.usedGrid t F, P.macroStep t ^4 * F.val (P.meshPose t i) : ℝ) : ℂ))
      atTop (𝓝 ((∫ x,F.val x:ℝ):ℂ)) := Complex.continuous_ofReal.continuousAt.tendsto.comp
        (thin_integrate_grid P F F.val F.smooth.continuous subset_closure)
  exact he.congr fun t => Complex.ofReal_sum _ _

lemma thin_activation_abs : Tendsto (fun t => ∑ i∈ P.usedGrid t F, ‖P.activation t F i‖)
    atTop (𝓝 (∫ x, ‖F.val x‖)) := by
  have he : Function.support (fun x => ‖F.val x‖) ⊆ tsupport F.val := fun x h =>
    subset_closure ((norm_ne_zero_iff).mp h)
  refine (thin_integrate_grid P F _ F.smooth.continuous.norm he).congr fun t=>?_
  refine Finset.sum_congr rfl fun i h=>?_
  rw [activation, Complex.norm_real, norm_mul, Real.norm_of_nonneg (pow_nonneg (P.macroStep_pos _).le 4)]

/-- Wall-support licenses. Use any η fitting the test; we'll buy the entire stencil
inside the boxes separately (`spacePrice`). -/
def thinPositive (F:SampleDose)(η:ℝ≥0) : Prop := ∀ x∈tsupport F.val, (η:ℝ)≤x (3:Axis)
def thinNegative (F:SampleDose)(η:ℝ≥0) : Prop := ∀ x∈tsupport F.val, x (3:Axis) ≤ -(η:ℝ)
lemma thin_flip_positive (η:ℝ≥0)(v:thinNegative F η) : thinPositive (flipDose F 3) η := by
  intro x h
  have he: (poseMirror 3) x ∈ tsupport F.val := (show x∈ (poseMirror 3) ⁻¹' tsupport F.val from flipBudget .. ▸ h)
  have q:= v ((poseMirror 3) x) he
  change opposeR 3 x 3 ≤ -(η:ℝ) at q
  rwa [show opposeR 3 x 3 = - x 3 from if_pos rfl, neg_le_neg_iff] at q
lemma thin_flip_mass : (∫ x,(flipDose F 3).val x) = ∫ x,F.val x :=
  (show MeasurePreserving (poseMirror 3).toMeasurableEquiv volume volume from opposite_money 3).integral_comp' F.val
end mass

section
private lemma thin_heat_bound {X:Hilbert} {j:Axis} (p:OS.Semigroup X j) (ω:X)
    (h:∀ t:ℝ≥0,p.E t ω=ω)(U:X.Op)(u:∀ x:X, ‖U x‖=‖x‖)(w:U ω=ω)
    (z:ℂ)(x:X)(a t:ℝ≥0)(r:a≤t) :
    ‖U (p.E t x)-z • ω‖ ≤ ‖p.E a x - z • ω‖ := by
  have ht (b) : p.E b (x - z • ω) = p.E b x - z • ω := by rw [map_sub,map_smul,h]
  rw [show U (p.E t x)-z • ω= U (p.E t x - z • ω) by rw [map_sub,map_smul,w],u, ← ht,← ht]
  exact p.norm_decrease (x - z • ω) r

private lemma thin_sum_bound {X:Hilbert} {ι : Type} (A:Finset ι) (p:ι→ℂ)
    (f:ι→X) (y:X)(w:ℝ)(e:∀ i∈A,‖f i-y‖≤ w) :
    dist ((∑ i∈A,p i) • y) (∑ i∈A,p i • f i) ≤ (∑ i∈A,‖p i‖)*w := by
  rw [dist_comm,dist_eq_norm,Finset.sum_smul,←Finset.sum_sub_distrib, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i h=>?_))
  rw [← smul_sub,norm_smul]
  exact mul_le_mul_of_nonneg_left (e i h) (norm_nonneg _)

variable {P : Spine} {x : P.Spectrum0 3}
local notation "ξ" => P.advocate 3 x 3
local notation "H" => P.ColorHil 3 ξ
local notation "ω" => P.colorZero 3 ξ
local notation "S" => P.physicalEnergy 3 ξ
local notation "E" => (S).E
local notation "Γ" => P.truck 3 ξ
local notation "G" => P.ManyF 3 ξ
local notation "Ω" => P.heaven 3 ξ
local notation "R" => P.seasons 3 ξ
local notation "π'" => P.wealth 3 ξ
local notation "λ'" => (P.enter 3 ξ)

lemma thin_grid_distance (F:SampleDose){η:ℝ≥0}(p:thinPositive F η)
    (z:ℂ) (A:P.Apron)(eA:P.birthF 3 A.s A.F)(t:ℕ) :
    dist ((∑ i∈P.usedGrid t F,P.activation t F i) • (z • ω)) (P.thinGridKet x t A eA F) ≤
      (∑ i∈P.usedGrid t F, ‖P.activation t F i‖)* ‖E η (P.thinOrigin x A eA)- z • ω‖:= by
  refine thin_sum_bound _ (P.activation t F) (P.thinGridRay x t A eA) (z • ω) _ ?_
  intro i h
  let a:= (P.meshPose t i) 3; let u:=P.vtile t i
  have ha:(η:ℝ) ≤ a := p _ ((P.usedPose t F i).1 h)
  have he: η ≤ a.toNNReal := by
    apply NNReal.coe_le_coe.mp; rw [Real.coe_toNNReal _ (η.property.trans ha)]; exact ha
  exact thin_heat_bound S ω (P.sector_hot 3 ξ) (Γ u) (P.truck_norm 3 ξ u) (P.truck_empty ..)
    z _ _ _ he

/-- UV of smearing can go to its limit first with fixed width. Pass the *bound*
through that limit for each width. -/
lemma thin_cont_distance (F:SampleDose){η:ℝ≥0}(p:thinPositive F η)
    (z:ℂ) (A:P.Apron)(eA:P.birthF 3 A.s A.F)(J:P.Ellis 3 x) :
    dist (((∫ x,F.val x:ℝ):ℂ) • (z • Ω)) (P.thinKet x A eA F) ≤
      (∫ x, ‖F.val x‖) * ‖E η (P.thinOrigin x A eA)- z • ω‖ := by
  have hs := (P.thin_activation_mass F).smul_const (z • ω)
  have he := Filter.Tendsto.dist hs (P.thin_to_ket x A eA F J)
  have ht := le_of_tendsto_of_tendsto he ((P.thin_activation_abs F).mul_const
      ‖E η (P.thinOrigin x A eA)- z • ω‖) (Eventually.of_forall fun t=>
        thin_grid_distance (x:=x) F p z A eA t)
  let v:G:= (( (∫ x,F.val x:ℝ):ℂ) • (z • Ω))
  let s := P.thinKet x A eA F
  exact ((λ').dist_map v s).symm.le.trans (show dist (λ' v) (λ' s) ≤ _ from ht)

variable (F:SampleDose){η:ℝ≥0}(p:thinPositive F η)(z:ℂ)
    (A:ℕ→P.Apron)(eA:∀ i, P.birthF 3 (A i).s (A i).F)
include p

/-- The physical sweeps can simultaneously thin the mark's own support and still approach a
    well-defined one-field vector on this very state, no subsequence extraction.
    This lemma upgrades convergence of the *unsmeared* heat-damped views. -/
lemma thin_grid_ket_tendsto
    (h:Tendsto (fun i => E η (P.thinOrigin x (A i) (eA i))) atTop (𝓝 (z • ω)))
    (t:ℕ→ℕ)(u:Tendsto t atTop atTop):
    Tendsto (fun i => P.thinGridKet x (t i) (A i) (eA i) F) atTop
      (𝓝 (((∫ x,F.val x:ℝ):ℂ) • (z • ω))) := by
  have he : Tendsto (fun i => (∑ k ∈ P.usedGrid (t i) F,P.activation (t i) F k) • (z • ω))
      atTop (𝓝 (((∫ x,F.val x:ℝ):ℂ) • (z • ω))) := ((P.thin_activation_mass F).smul_const (z • ω)).comp u
  apply he.congr_dist
  have hv : Tendsto (fun i => ‖E η (P.thinOrigin x (A i) (eA i))-z • ω‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp h
  have hsq := ((P.thin_activation_abs F).comp u).mul hv
  rw [mul_zero] at hsq
  exact squeeze_zero (fun _=>dist_nonneg) (fun i=>thin_grid_distance F p z (A i) (eA i) (t i)) hsq

lemma thin_ket_tendsto
    (h:Tendsto (fun i => E η (P.thinOrigin x (A i) (eA i))) atTop (𝓝 (z • ω))) (J:P.Ellis 3 x):
    Tendsto (fun i => P.thinKet x (A i) (eA i) F) atTop
      (𝓝 (((∫ x,F.val x:ℝ):ℂ) • (z • Ω))) := by
  let v:G:= (((∫ x,F.val x:ℝ):ℂ) • (z • Ω))
  refine (tendsto_const_nhds (x:=v)).congr_dist ?_
  have hv : Tendsto (fun i => ‖E η (P.thinOrigin x (A i) (eA i))-z • ω‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp h
  have he:= hv.const_mul (∫ x, ‖F.val x‖); rw [mul_zero] at he
  exact squeeze_zero (fun _=>dist_nonneg) (fun i=> thin_cont_distance F p z (A i) (eA i) J) he

end

#print axioms thin_grid_ket_tendsto
#print axioms thin_ket_tendsto
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

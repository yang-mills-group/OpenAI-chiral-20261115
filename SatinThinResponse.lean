import SatinFixedContrastNovember4

import SatinThinKernel
import SatinThinSweep

/-!
# A thin bilocal-composite experiment: responses

`ThinSensor` and the existence theorem below cover a general class of
**vanishing thickness** experiments with *already purchased* damped-view
and Sensor estimates. See the application for *actually realizing them*.
In this result we are especially interested in the one- and two-point
Euclidean probes on this state. Provide the counter-calculation also for
the raw gauge–matter factor comparator, not just because of any orthogonal
axis interpretation of the operators but by tracking actual *issued* charges.
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

section
variable (P : Spine) (x : P.Spectrum0 3)
local notation "K" => P.calibration
local notation "ξ" => P.advocate 3 x 3
local notation "R" => P.seasons 3 ξ
local notation "G" => P.ManyF 3 ξ
local notation "Ω" => P.heaven 3 ξ
local notation "H" => P.ColorHil 3 ξ
local notation "ω" => P.colorZero 3 ξ
local notation "E" => (P.physicalEnergy 3 ξ).E
local notation "λ'" => (P.enter 3 ξ)
local notation "T" => P.Test

/-- Post-height (t) comparison. Use the purchased Comparison existence in the given project
and also keep its uniqueness. Thus no need to ask for a rechoice/matching of a different
factorized regulator ensemble. In a response on the thin fields (smeared probes on the
vacuum) we want exactly this canonical prediction in the raw dictionary at `t`, on the
same *gauge-invariant regulator polynomials*, then take limits of the predictions too. -/
def thinSplit (t:ℕ) : T →ₗ[ℂ] ℂ := (P.comparator t x).choose
lemma thin_comparator_LocalFieldBounds (t:ℕ) : Comparison K (P.singleState 3 t x) (P.thinSplit x t) ∧
    (P.thinSplit x t) 1=1 ∧ GaugeWard K (P.thinSplit x t) ∧ MatterWard K (P.thinSplit x t) :=
  (P.comparator t x).choose_spec
lemma thin_comparator_only (t:ℕ) (X:T→ₗ[ℂ]ℂ) (v:Comparison K (P.singleState 3 t x) X) :
    X=P.thinSplit x t := v.unique K (P.singleState 3 t x) (P.thin_comparator_LocalFieldBounds x t).1
lemma thin_split_is_raw (t:ℕ) (f g:T) (p:PureGauge K f)(q:PureMatter K g) :
    P.thinSplit x t (f*g)=P.singleState 3 t x f * P.singleState 3 t x g := by
  let h := (P.thin_comparator_LocalFieldBounds x t).1
  rw [h.factors f g p q, h.link f p,h.matter g q]

lemma thin_joint_calculation (f:T) (K':P.Register) (t:ℕ) :
    P.singleState 3 t x f = P.chi 3 x (P.reading 3 t f) ∧
    P.singleState 3 t x f = P.spirits K' 3 x (P.slotHole t f) := ⟨rfl,(P.oneCup K' 3 x t f).symm⟩

private lemma thin_split_one (t:ℕ) (F:SampleDose)(W:Bool) (A:P.Apron)(h:P.Sensor A W)
    (p:A.s≤t)(X:T→ₗ[ℂ]ℂ)(e:Factors K X)(u:MatterWard K X ∨ GaugeWard K X) : X (P.prepared t A F)=0 := by
  unfold prepared; rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  have hY : X (P.issuing t A i) = 0 := by
    simpa only [List.map_nil,List.prod_nil,mul_one] using P.msplit W t e u A i h p [] (by simp)
  rw [map_smul, hY, smul_zero]

abbrev thicknessZero (P:Spine)(A:ℕ→P.Apron) :=
  ∀ j:Axis, Tendsto (fun i => (A i).realWidth P j) atTop (𝓝 0)
/-- Define a sensor series and capture its positive physical gap property separately from the
    convergence theorem. Keep same character, weights, widths before poses! -/
structure ThinSensor (P:Spine)(x:P.Spectrum0 3)(V:ℕ→P.Apron)
    (h:∀ i,P.birthF 3 (V i).s (V i).F)(Z:Lead.Clan)(z:ℂ) : Prop where
  heights : Tendsto (fun i => (V i).s) atTop atTop
  zeroWidth : P.thicknessZero V
  orth : ∀ᶠ i in atTop, P.Sensor (V i) Z.2
  heat (η:ℝ≥0) (p:0<η) : Tendsto (fun i => (P.physicalEnergy 3 (P.advocate 3 x 3)).E η
                   (P.thinOrigin x (V i) (h i))) atTop (𝓝 (z • P.colorZero 3 (P.advocate 3 x 3)))

/-- per-body *intrinsic* support control, including issuing at EVERY fine height and grid pose -/
def ThinFootprints (P:Spine)(A:ℕ→P.Apron) (i:ℕ) (δ:ℝ) : Prop :=
  (∀ p, P.Aperture (A i) p ⊆ Metric.ball p δ) ∧
  (∀ t, (A i).s≤t→∀ j, P.issuing t (A i) j ∈ enclave P.calibration ∧
    P.asked_at t (P.issuing t (A i) j) (Metric.ball (P.meshPose t j) δ)) ∧
  (∀ F:SampleDose, ∀ t, (A i).s≤t→ P.prepared t (A i) F ∈ enclave P.calibration ∧
    P.asked_at t (P.prepared t (A i) F) (P.spacePrice (A i) F))
theorem thin_qualify (A:ℕ→P.Apron)(h:P.thicknessZero A)(δ:ℝ)(p:0<δ) :
    ∀ᶠ i in atTop, P.ThinFootprints A i δ := by
  filter_upwards [eventually_all.mpr (fun j:Axis => Metric.tendsto_nhds.mp (h j) δ p)] with i e
  have h (r:Vantage) : P.Aperture (A i) r ⊆ Metric.ball r δ := by
    intro y u
    apply (dist_pi_lt_iff p).2
    intro j
    have ht: dist ((A i).realWidth P j) 0< δ:= e j
    rw [Real.dist_eq, sub_zero, abs_of_pos ((A i).real_width_pos P j)] at ht
    exact le_of_eq (Real.dist_eq ..) |>.trans_lt ((u j).trans_lt ht)
  refine ⟨h, fun t p j=> ?_, fun F t p=>⟨P.prepared_color t (A i) F,P.prepared_at t (A i) F p⟩⟩
  exact ⟨P.issuing_color t j _, _, P.issuing_support t j (A i), (P.inside_now t j (A i) p).trans (h _)⟩

/-- Supports of smears within open sets, not just limited by price-community notation. -/
theorem thin_inside (A:ℕ→P.Apron)(h:P.thicknessZero A)(U:Set Vantage) (e:IsOpen U)
    (F:SampleDose)(p:tsupport F.val ⊆ U) : ∀ᶠ i in atTop, P.spacePrice (A i) F ⊆ U := by
  obtain ⟨δ,a,hδ⟩ := F.budget.exists_thickening_subset_open e p
  filter_upwards [P.thin_qualify A h δ a] with i t
  intro y hy; obtain ⟨q,u,v⟩:= Set.mem_iUnion₂.mp hy
  exact hδ (Metric.mem_thickening_iff.mpr ⟨q,u, t.1 q v⟩)

-- Package exact finite-t assertions together with wall and pin assignment, for one pair
-- at any eligible width. Supports of the SMEARS are compact. Their smearands stay in
-- ThinFootprints (arbitrarily small assigned around each actual position).
section point
variable (A B:P.Apron)(eA:P.birthF 3 A.s A.F)(eB:P.birthF 3 B.s B.F)(F U:SampleDose)
local notation "ζ₁" => (A.kiss P 3)
local notation "s₁" t:max => P.prepared t ζ₁ F
local notation "s₂" t:max => P.prepared t B U
local notation "g₁" t:max => P.thinGridKet x t A eA (flipDose F 3)
local notation "g₂" t:max => P.thinGridKet x t B eB U
local notation "X" => P.thinKet x A eA (flipDose F 3)
local notation "Y" => P.thinKet x B eB U
local notation "p[" t "]" => P.singleState 3 t x

structure ThinSeam : Prop where
  beforeWall : P.WallBefore ζ₁ F 0
  afterWall : P.WallAfter B U 0
  ordered : Disjoint (P.spacePrice ζ₁ F) (P.spacePrice B U)
  colored t : s₁ t ∈ enclave P.calibration ∧ s₂ t ∈ enclave P.calibration
  region t (h:A.s ≤ t)(p:B.s ≤ t) : P.asked_at t (s₁ t) (P.spacePrice ζ₁ F) ∧
                                      P.asked_at t (s₂ t) (P.spacePrice B U)
  earlier t (h:A.s ≤ t) : ∃ k:P.Test, P.reflectTest 3 k = s₁ t ∧ ∃ h:P.birthF 3 t k, P.viewF 3 ξ t h=g₁ t
  laterK t (h:B.s ≤ t) : ∃ h:P.birthF 3 t (s₂ t), P.viewF 3 ξ t h=g₂ t
  split t (h:A.s≤t)(p:B.s≤t)(X₀:T→ₗ[ℂ]ℂ)(v:Factors K X₀)(w:MatterWard K X₀ ∨ GaugeWard K X₀) :
      X₀ (s₁ t)=0 ∧ X₀ (s₂ t)=0 ∧ X₀ (s₁ t * s₂ t)=0
  raw t (h:A.s≤t)(p:B.s≤t) : p[t] (s₁ t * s₂ t)=inner ℂ (g₁ t) (g₂ t)
  gridEarly : Tendsto (fun t:ℕ=>g₁ t) atTop (𝓝 (λ' X))
  gridLate : Tendsto (fun t:ℕ=>g₂ t) atTop (𝓝 (λ' Y))
  price : Tendsto (fun t=>p[t] (s₁ t * s₂ t)) atTop (𝓝 (inner ℂ X Y))
  single : Tendsto (fun t=>p[t] (s₁ t)) atTop (𝓝 (star (inner ℂ Ω X))) ∧
    Tendsto (fun t=>p[t] (s₂ t)) atTop (𝓝 (inner ℂ Ω Y))
  continuousKernel : inner ℂ X Y = ∫ p,∫ q,(F.val p:ℂ)*(U.val q:ℂ)*
    P.commonWell 3 x (usher (A.kiss P 3) B) (usher p q) [false,true]

lemma thin_price_seam {W W':Bool}(p:P.Sensor A W)(q:P.Sensor B W')
    (a:P.WallBefore A F 0)(b:P.WallAfter B U 0)(J:P.Ellis 3 x):
    P.ThinSeam x A B eA eB F U := by
  have e:=P.test_apart ζ₁ F 0 B U a b
  have h:=P.sensor_mirror W 3 A p
  refine ⟨a,b,e,fun t=>⟨P.prepared_color t _ F,P.prepared_color t _ U⟩,
    fun t p q=>⟨P.prepared_at t _ F p,P.prepared_at t _ U q⟩,
    fun t h=>P.thin_grid_flip x t A eA F a h,fun t h=>P.thin_grid_view x t B eB U b h,
    fun t u r X' v m=> ⟨thin_split_one P t F W _ h u X' v m,
                           thin_split_one P t U W' B q r X' v m,P.split_test t _ F B U e u r W h X' v m⟩,
    fun t h p=>P.thin_pair_grid x t A eA F B eB U a b h p,
    P.thin_to_ket x A eA (flipDose F 3) J,P.thin_to_ket x B eB U J,P.thin_pair_kets x A eA F B eB U a b J,
    ⟨P.thin_early_single x A eA F a J,P.thin_late_single x B eB U b J⟩,P.thin_contPrice x A eA B eB F U a b J⟩
end point

-- response package for the pair. This definition is *not* a claim about any operators on
-- a common time-zero unbounded-operator domain, etc. `late` records the one- & two-point
-- identifications from costed grid tests when taking the grid positions to the smooth tests
-- (on the elected vacuum), width fixed. Then `leftC,rightC,reads` take that physical width
-- to zero (`thinner`). And `duringGrid` strengthens both limits. **In addition** direct
-- comparison of the actual and canonical raw-factorized predictions is done on the same
-- marked inputs at `t`. `leftC` is an actual vector of P's Hilbert space, not an ultrapower,
-- with convergence in the strong/norm topology. Earlier fields are specified by adjoint
-- representatives. These are smeared Euclidean fields on Ω (axis 3, in the separated
-- one- & two-point sense).

/-- Use for earlier price (then take complex conjugate) or later. -/
def thinFieldWeight (z:ℂ)(F:SampleDose) : ℂ := (∫ x,F.val x : ℝ) * z

section series
variable (F U: SampleDose) (A B:ℕ→P.Apron)
local notation "A[" i "]" => (A i).kiss P 3
variable (eA:∀ i,P.birthF 3 (A i).s (A i).F)(eB:∀ i,P.birthF 3 (B i).s (B i).F)
variable (w z:ℂ)
local notation "s₁" t:max i:max => P.prepared t (A[i]) F
local notation "s₂" t:max i:max => P.prepared t (B i) U
local notation "g₁" t:max i:max => P.thinGridKet x t (A i) (eA i) (flipDose F 3)
local notation "g₂" t:max i:max => P.thinGridKet x t (B i) (eB i) U
local notation "X" i:max => P.thinKet x (A i) (eA i) (flipDose F 3)
local notation "Y" i:max => P.thinKet x (B i) (eB i) U
local notation "p[" t "]" => P.singleState 3 t x
local notation "W" => thinFieldWeight w F
local notation "Z" => thinFieldWeight z U

structure ThinPair : Prop where
  thinner (δ:ℝ)(p:0<δ): ∀ᶠ i in atTop, P.ThinFootprints (fun j=> A[j]) i δ ∧
                                           P.ThinFootprints B i δ
  late : ∀ᶠ i in atTop, P.ThinSeam x (A i) (B i) (eA i) (eB i) F U
  leftC : Tendsto (fun i=> X i) atTop (𝓝 (W • Ω))
  rightC : Tendsto (fun i=> Y i) atTop (𝓝 (Z • Ω))
  readSingles : Tendsto (fun i=>star (inner ℂ Ω (X i))) atTop (𝓝 (star (W))) ∧
                Tendsto (fun i=>inner ℂ Ω (Y i)) atTop (𝓝 Z)
  reads : Tendsto (fun i=>inner ℂ (X i) (Y i)) atTop (𝓝 (star (W)*Z))
  duringGrid (t:ℕ→ℕ)(h:∀ᶠ i in atTop, (A i).s≤ t i ∧ (B i).s≤ t i) :
      Tendsto (fun i=>g₁ (t i) i) atTop (𝓝 (W • ω)) ∧
      Tendsto (fun i=>g₂ (t i) i) atTop (𝓝 (Z • ω)) ∧
      Tendsto (fun i=>p[t i] (s₁ (t i) i)) atTop (𝓝 (star (W))) ∧
      Tendsto (fun i=>p[t i] (s₂ (t i) i)) atTop (𝓝 Z) ∧
      Tendsto (fun i=>p[t i] (s₁ (t i) i * s₂ (t i) i)) atTop (𝓝 (star (W)*Z))
  factorized : ∀ᶠ i in atTop,∀ t, (A i).s≤t → (B i).s≤t → P.thinSplit x t (s₁ t i*s₂ t i)=0

section readiness
private lemma inner_weight {Q:Hilbert}(ω':Q)(h:‖ω'‖=1) (a:ℂ) : inner ℂ ω' (a • ω')=a := by
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]; simp [h]
private lemma receipt_weight {Q:Hilbert}(ω':Q)(h:‖ω'‖=1) (a b:ℂ) :
    inner ℂ (a • ω') (b • ω')= star a * b := by rw [inner_smul_left,inner_weight ω' h]; rfl

private lemma during (J:P.Ellis 3 x) {i j:Lead.Clan} (p:P.ThinSensor x A eA i w)
    (q:P.ThinSensor x B eB j z) {δ:ℝ≥0} (v:0<δ) (f:thinNegative F δ)(u:thinPositive U δ) :
    ∀ᶠ i in atTop, P.ThinSeam x (A i) (B i) (eA i) (eB i) F U := by
  filter_upwards [(p.zeroWidth 3).eventually (gt_mem_nhds (show (0:ℝ) < δ from v)),
        (q.zeroWidth 3).eventually (gt_mem_nhds (show (0:ℝ) < δ from v)), p.orth, q.orth] with i a b p q
  change (A i).realWidth P 3 < _ at a
  change (B i).realWidth P 3 < _ at b
  exact P.thin_price_seam x _ _ _ _ F U p q (fun k h => by linarith only [a,f k h])
        (fun k h=> (zero_add _).trans_lt (b.trans_le (u k h))) J
end readiness

variable (J:P.Ellis 3 x) {i j:Lead.Clan} (p:P.ThinSensor x A eA i w)
    (q:P.ThinSensor x B eB j z) {δ:ℝ≥0} (v:0<δ) (f:thinNegative F δ)(u:thinPositive U δ)
include J p q v f u

private lemma both_orth_limit (t:ℕ→ℕ)(g:∀ᶠ i in atTop, (A i).s≤t i ∧ (B i).s≤t i) :
      Tendsto (fun i=>g₁ (t i) i) atTop (𝓝 (W • ω)) ∧
      Tendsto (fun i=>g₂ (t i) i) atTop (𝓝 (Z • ω)) ∧
      Tendsto (fun i=>p[t i] (s₁ (t i) i)) atTop (𝓝 (star (W))) ∧
      Tendsto (fun i=>p[t i] (s₂ (t i) i)) atTop (𝓝 Z) ∧
      Tendsto (fun i=>p[t i] (s₁ (t i) i * s₂ (t i) i)) atTop (𝓝 (star (W)*Z)) := by
  have hd:Tendsto t atTop atTop:= tendsto_atTop_mono' _ (g.mono fun _ h=>h.1) p.heights
  have hx:= thin_grid_ket_tendsto (flipDose F 3) (thin_flip_positive F _ f) w A _ (p.heat δ v) t hd
  have he:= thin_grid_ket_tendsto U u z B _ (q.heat δ v) t hd
  -- compose scalars
  have hl:Tendsto (fun i=>g₁ (t i) i) atTop (𝓝 (W • ω)) := by
    rw [thinFieldWeight,mul_smul]; rw [thin_flip_mass] at hx; exact hx
  have hz:Tendsto (fun i=>g₂ (t i) i) atTop (𝓝 (Z • ω)) := by rw [thinFieldWeight,mul_smul]; exact he
  have hg := (during P x F U A B eA eB w z J p q v f u).and g
  have norm: ‖ω‖=1:= P.norms_color ..
  refine ⟨hl,hz,?_,?_,?_⟩
  · have h := ((show Tendsto (fun (_:ℕ)=>ω) atTop (𝓝 ω) from tendsto_const_nhds).inner (𝕜:=ℂ) hl).star
    rw [inner_weight (Q:=H) ω norm] at h
    exact h.congr' (hg.mono fun i e=> (P.thin_early_single_grid x (t i) (A i) (eA i) F e.1.beforeWall e.2.1).symm)
  · have h := (show Tendsto (fun (_:ℕ)=>ω) atTop (𝓝 ω) from tendsto_const_nhds).inner (𝕜:=ℂ) hz
    rw [inner_weight (Q:=H) ω norm] at h
    exact h.congr' (hg.mono fun i e=> (P.thin_late_single_grid x (t i) (B i) (eB i) U e.1.afterWall e.2.2).symm)
  have h:= hl.inner (𝕜:=ℂ) hz
  rw [receipt_weight (Q:=H) ω norm] at h
  exact h.congr' (hg.mono fun i e => (e.1.raw (t i) e.2.1 e.2.2).symm)

lemma buys_thin_pair : P.ThinPair x F U A B eA eB w z := by
  have ht:=during P x F U A B eA eB w z J p q v f u
  have h₁:Tendsto (fun i=> X i) atTop (𝓝 (W • Ω)) := by
    have he:=thin_ket_tendsto (flipDose F 3) (thin_flip_positive F _ f) w A _ (p.heat _ v) J
    rw [thin_flip_mass] at he; rw [thinFieldWeight,mul_smul]; exact he
  have h₂:Tendsto (fun i=> Y i) atTop (𝓝 (Z • Ω)) := by
    rw [thinFieldWeight,mul_smul]; exact thin_ket_tendsto U u z B _ (q.heat _ v) J
  have he:= h₁.inner (𝕜:=ℂ) h₂
  have h: ‖Ω‖=1:= P.stone_norm ..
  rw [receipt_weight (Q:=G) Ω h] at he
  refine ⟨fun δ v=> (P.thin_qualify (fun i=> A[i]) p.zeroWidth δ v).and (P.thin_qualify B q.zeroWidth δ v),
    ht,h₁,h₂,?_,he,both_orth_limit P x F U A B eA eB w z J p q v f u,ht.mono ?_⟩
  · have ht:Tendsto (fun (_:ℕ)=> Ω) atTop (𝓝 Ω) := tendsto_const_nhds
    have hp:= ht.inner (𝕜:=ℂ) h₁; have hg:= ht.inner (𝕜:=ℂ) h₂
    rw [inner_weight (Q:=G) Ω h] at hp hg; exact ⟨hp.star,hg⟩
  exact fun i h t p q=> (h.split t p q _ (P.thin_comparator_LocalFieldBounds x t).1.factors
      (Or.inr (P.thin_comparator_LocalFieldBounds x t).2.2.1)).2.2
omit J p q v f u
end series
end
#print axioms buys_thin_pair
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

import SatinFixedContrastNovember4

import SatinThinResponse

/-!
# Apply the estimate to actual family signals

This is the unconditional application (no hypothesis of convergence, interaction or
UV purchases not on the very same state). Keep the two tests of `SatinFixedContrast`.
Keep both of their boxes fixed, and the coupling and normalization (singleState,
on this very x). At the two test centers use genuine intrinsically shrinking
`thinMat`s (first test uses its Euclidean adjoint). The measured quantities and
support permits are all given in `ThinSeam` and `ThinPair`. Include also the entire
comparison in the limit and before the limit. This is NOT a nonzero
**spatially connected** reading; we prove an obstruction in that regard at this
normalization (including for trying to use exactly the high-resolution members
of the original probe recipe). It is a nonzero gauge–matter interaction in the
prescribed **actual minus raw factorized** sense (NOT by spatial factorization).
See notes on limitations in the proof. This file does not address
changing the internal normalization to target a nonzero spatially connected result.
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

variable (P:Spine)

/-- A shrinking physical Wilson bilocal composite in each chiral family. In fact use
exactly the front half of the probe in `experimentBody` -- no pretending that that
entire mark is an elementary field independent of its internal separation! **Multiplicative**
renormalization: take `Lead.sing n false`, before coloring & posing, no additive counterterm.
No field-strength factors applied later in taking either limit. We'll use `s=c i,n=r i`.
-/
def thinMat (Z:Lead.Clan)(s n:ℕ): P.Apron :=
  { P.experimentBody Z s n with
    F:=P.frontMat Z n
    bay:= (tallerBay P.calibration (P.flash n).patio true Finset.subset_union_left)
            (P.visibility Z n)
    realM:= P.front_real Z n }

theorem thin_regulator_formula (Z:Lead.Clan)(s n:ℕ)(m:Side)(X:Fields (P.calibration.c m)) :
    (P.thinMat Z s n).F.val m X =
      Lead.sing n false • ∑ i∈Window.colors Z,∑ j∈Window.colors Z,
        (Lamour.Bridge.Celeste.coilFlag (P.flash n) i j (onC (P.calibration.c m) X.1)) •
         (Fock.remove (basisC (P.calibration.c m) (P.flash n).death 2 j)*
          create (basisC (P.calibration.c m) (P.flash n).birth 0 i)) := P.front_read Z n m X

section both
variable (Z W: Lead.Clan)(c r:ℕ→ℕ)
local notation "A[" i "]" => P.thinMat Z (c i) (r i)
local notation "A'[" i "]" => P.experimentBody Z (c i) (r i)
local notation "B[" i "]" => P.thinMat W (c i) (r i)
local notation "B'[" i "]" => P.experimentBody W (c i) (r i)
lemma thin_mat_born (i:ℕ) : P.birthF 3 (A[i]).s (A[i]).F := P.brightC Z (c i) (r i)
lemma thin_mat_senses (i:ℕ)(h:P.calibration.ℓ < r i) : P.Sensor A[i] Z.2 := by
  let V:= P.flash (r i); let S:=({nodeC V.birth}:Finset Cover); let T:=({nodeC V.death}:Finset Cover)
  have d:S⊆ V.patio:= Finset.singleton_subset_iff.mpr (Lamour.Bridge.Celeste.porchBorn V)
  have e:T⊆ V.patio:= Finset.singleton_subset_iff.mpr (Lamour.Bridge.Celeste.porchGone V)
  exact Submodule.subset_span (show _∈_ from
    ⟨S,T,V.patio,Finset.union_subset d e, Finset.subset_union_left,P.pocket_gap (c i) (r i) h,
      P.front_charge Z (r i),P.front_real Z (r i)⟩)

local notation "eA" => P.thin_mat_born Z c r
local notation "eB" => P.thin_mat_born W c r
variable (x:P.Spectrum0 3){K:P.Register}{J:P.Ellis 3 x}(C: P.Experiment K c r x J)
include C
local notation "z₁" => (purePrice Z:ℂ)
local notation "z₂" => (purePrice W:ℂ)
lemma thin_front_sensor : P.ThinSensor x (fun i=>A[i]) eA Z z₁ :=
  ⟨C.launch.smaller.tendsto_atTop,limit_width C.launch,
   (C.launch.eager.tendsto_atTop.eventually (eventually_gt_atTop P.calibration.ℓ)).mono (P.thin_mat_senses Z c r),
   fun η p=> thin_front_shard_tendsto Z C (fun _=>η)
      (thin_compare_dew C p _ (Eventually.of_forall fun _=>le_refl η))⟩
lemma thin_old_sensor : P.ThinSensor x (fun i=> A'[i]) (fun i=>P.body_birth Z (c i) (r i)) Z 0 := by
  refine ⟨C.launch.smaller.tendsto_atTop,limit_width C.launch,
    (C.launch.eager.tendsto_atTop.eventually (eventually_gt_atTop P.calibration.ℓ)).mono (fun i h=>P.body_senses Z _ _ h),
    fun η p=>?_⟩
  rw [zero_smul]; exact thin_old_shard_tendsto Z C _ (thin_compare_dew C p _ (Eventually.of_forall fun _=>le_refl η))
lemma thin_studies (F U:SampleDose)(δ:ℝ≥0)(p:0<δ)(e:thinNegative F δ)(v:thinPositive U δ) :
    P.ThinPair x F U (fun i=> A[i]) (fun i=>B[i]) eA eB z₁ z₂ ∧
    P.ThinPair x F U (fun i=>A'[i]) (fun i=>B'[i]) (fun i=>P.body_birth Z (c i) (r i))
      (fun i=>P.body_birth W (c i) (r i)) 0 0:=
  ⟨P.buys_thin_pair x F U _ _ _ _ z₁ z₂ J (P.thin_front_sensor Z c r x C)
        (P.thin_front_sensor W c r x C) p e v,
   P.buys_thin_pair x F U _ _ _ _ 0 0 J (P.thin_old_sensor Z c r x C)
        (P.thin_old_sensor W c r x C) p e v⟩

-- Further point price observation for the interpretation and to test the changing footprints
-- against the reference `the construction notes` obstruction. Applies to a genuine pair at any
-- **physical** positive time separation. No payment on center-coincidence.
local notation "ξ" => P.advocate 3 x 3
local notation "G" => P.ManyF 3 ξ
local notation "Ω" => P.heaven 3 ξ
local notation "R" => P.seasons 3 ξ
local notation "E" => (R).E
local notation "V" => P.cartage 3 ξ
private lemma thin_drive_limit (a:ℕ→ℝ≥0)(v:Tendsto (fun i=>(a i:ℝ)/P.dew (c i) (r i)) atTop atTop)
    (p:ℕ→Vantage) : Tendsto (fun i => V (p i) (E (a i) (P.lucid x Z (c i) (r i)))) atTop (𝓝 (z₁ • Ω)) := by
  let y(i):= E (a i) (P.lucid x Z (c i) (r i)); let u(i):=V (p i)
  let Z':G:= z₁ • Ω
  have he:Tendsto y atTop (𝓝 Z'):= thin_front_lucid_tendsto Z C _ v
  rw [tendsto_iff_norm_sub_tendsto_zero] at he ⊢
  refine he.congr fun i=>?_
  have ht:u i Z'=Z':= (map_smul (u i) z₁ Ω).trans (congrArg (z₁ • ·) (P.cart_empty ..))
  exact ((P.cart_norm 3 ξ (p i) (y i-Z')).symm.trans (congrArg (norm) ((map_sub (u i) _ _).trans
    (congrArg ((u i) (y i)-·) ht))))
omit C in
private lemma thin_half_get {X:Hilbert}(R':OS.Semigroup X (3:Axis))(U:X.Op)(f g:X)(t:ℝ≥0)
    (h:∀ (u:ℝ≥0)(x:X), R'.E u (U x)= U (R'.E u x)) :
    inner ℂ f (U (R'.E t g))=inner ℂ (R'.E (t/2) f) (U (R'.E (t/2) g)) := by
  rw [OS.Semigroup.swing,h, ←ContinuousLinearMap.comp_apply (R'.E _),← R'.time,add_halves]
omit C in
lemma thin_single_vac(a b:ℂ): inner ℂ (a • Ω) (b • Ω)= star a*b := by
  rw [inner_smul_right,inner_smul_left, inner_self_eq_norm_sq_to_K,P.stone_norm 3 ξ]; simp [mul_comm]

lemma thin_kernel_far {d:ℝ}(hd:0<d)(p q:ℕ→Vantage)(h:∀ᶠ i in atTop, d ≤ q i 3 - p i 3):
    Tendsto (fun i=> P.commonWell 3 x (usher ((A[i]).kiss P 3) B[i]) (usher (p i) (q i)) [false,true])
      atTop (𝓝 (z₁*z₂)) := by
  let t(i:ℕ):=(q i 3-p i 3).toNNReal
  let a(i:ℕ):= t i /2
  have hD: d/2>0:=half_pos hd
  have hv:Tendsto (fun i=>(a i:ℝ)/P.dew (c i) (r i)) atTop atTop:=thin_compare_dew C (a:=⟨d/2,hD.le⟩) hD _
    (h.mono (fun i h'=> by
      apply NNReal.coe_le_coe.mp
      rw [show (a i:ℝ)=(q i 3-p i 3)/2 from ?_]; exact div_le_div_of_nonneg_right h' (zero_le_two)
      exact by unfold a t; rw [NNReal.coe_div, NNReal.coe_ofNat, Real.coe_toNNReal _ (hd.le.trans h')]))
  have he:= (thin_front_lucid_tendsto Z C a hv).inner (𝕜:=ℂ)
        (thin_drive_limit P W c r x C a hv (q-p))
  rw [P.thin_single_vac x, show star (z₁) = z₁ by simp] at he
  refine he.congr' ?_
  let w(i):= P.probeWidth (c i) (r i) 3
  have ht:Tendsto w atTop (𝓝 0):= limit_width C.launch 3
  filter_upwards [h, ht.eventually (gt_mem_nhds hD)] with i p' q'
  have v:p i 3+(A[i]).realWidth P 3 < q i 3-(B[i]).realWidth P 3:=by
    change p i 3+w i < q i 3-w i; linarith only [p',show w i < _ from q']
  exact ((P.thin_kernel x A[i] (eA i) B[i] (eB i) (p i) (q i) J v).trans
      (thin_half_get (X:=G) R (V (q i-p i)) _ _ (t i) (P.warm_drive 3 ξ (q i-p i)))).symm
omit C

end both
section publishedLab
-- include the EXACT comparison with both tests confined to the chosen two physical boxes.
local notation "X₋" => reviewEarlierBox
local notation "X₊" => reviewLaterBox
local notation "x₊" => reviewLaterBox.invites
local notation "x₋" => reviewEarlierBox.invites
variable (x:P.Spectrum0 3)(c r:ℕ→ℕ)
local notation "τ" => P.thinSplit x
local notation "K" => P.calibration
local notation "T" => P.Test
local notation "E[" i "]" => P.singleState 3 i x
variable (F U : SampleDose)
local notation "A" i:max => (fun Z=> P.thinMat Z (c i) (r i))
local notation "z[" Z "]" => (purePrice Z : ℂ)
local notation "ξ" => P.advocate 3 x 3
local notation "Ω" => P.heaven 3 ξ
omit P in
private lemma narrowSide (p:tsupport F.val ⊆ x₋)(q:tsupport U.val ⊆ x₊) : thinNegative F 1 ∧ thinPositive U 1 :=
  ⟨fun _ u=> ((p u (3:Axis) (Set.mem_univ _)).2).le, fun _ u=> ((q u (3:Axis) (Set.mem_univ _)).1).le ⟩

def thinJointMark (i t:ℕ) (Z W:Lead.Clan) : T := P.prepared t (((A i) Z).kiss P 3) F *
                                                       P.prepared t ((A i) W) U
def thinChargeMatrix (i t:ℕ) : CrossRead := Matrix.of (fun Z W=> E[t] (P.thinJointMark c r F U i t Z W) -
                                      τ t (P.thinJointMark c r F U i t Z W))
/-- This outer product is the exact table of total **differences with raw factorized**
    at the chosen normalized pair. Without normalization `ThinPair` gives arbitrary
    smooth-before-and-after prices, too. (`purePrice` means the microscopic calibration
    in the *actual* construction, not a value in the factorized predictor!) -/
def thinReadMatrix : CrossRead := Matrix.vecMulVec (fun Z:Lead.Clan=>z[Z]) (fun Z:Lead.Clan=>z[Z])
lemma thin_positive_entry (Z W:Lead.Clan) : 0 < (thinReadMatrix Z W).re := (show (0:ℝ)< purePrice Z*purePrice W from
  mul_pos (purePrice_p Z) (purePrice_p W)) |>.trans_eq (by change _=(z[Z]*z[W]).re; simp)
lemma thin_not_full_rank : ¬ ReadsSix thinReadMatrix := fun h=> h.1 (Matrix.det_vecMulVec ..)

private lemma normalWeight (q:F.Normalized)(z:ℂ) : thinFieldWeight z F = z := by
  unfold thinFieldWeight; rw [q.2,Complex.ofReal_one,one_mul]

variable {R:P.Register}{J:P.Ellis 3 x}(C:P.Experiment R c r x J) (p:tsupport F.val ⊆ x₋)(q:tsupport U.val ⊆ x₊)
include C p q

lemma thin_direct_table (f:F.Normalized)(u:U.Normalized)(t:ℕ→ℕ)(ht:∀ᶠ i in atTop,c i≤t i) :
    Tendsto (fun i=>P.thinChargeMatrix x c r F U i (t i)) atTop (𝓝 thinReadMatrix) := by
  refine tendsto_pi_nhds.mpr (fun Z=>tendsto_pi_nhds.mpr fun W=>?_)
  let V:= narrowSide F U p q; let Q:= (P.thin_studies Z W c r x C F U 1 zero_lt_one V.1 V.2).1
  let L i := P.thinJointMark c r F U i (t i) Z W
  have he:= (Q.duringGrid t (ht.mono fun i h=>⟨h,h⟩)).2.2.2.2
  rw [normalWeight F f, normalWeight U u, show star z[Z]=z[Z] by simp] at he
  refine he.congr' ?_
  filter_upwards [ht,Q.factorized] with i h e
  change E[t i] (L i)= E[t i] (L i)- τ (t i) (L i)
  rw [show τ (t i) (L i)=0 from e _ h h,sub_zero]

private lemma coarse_criterion (f:F.Normalized)(u:U.Normalized)(i j:Lead.Clan) :
    ∀ᶠ k in atTop, ∀ t, c k ≤ t →
      (thinReadMatrix i j).re/2 < (P.thinChargeMatrix x c r F U k t i j).re := by
  let K₀:=(thinReadMatrix i j).re/2; let g (n t:ℕ):=(P.thinChargeMatrix x c r F U n t i j).re
  -- select a witness refinement if there *is* a failure
  let t(k:ℕ) := if h: ∃ t≥ c k,g k t ≤ K₀ then Nat.find h else c k
  have ht(k:ℕ) : c k≤t k := by
    unfold t; split
    next h => exact (Nat.find_spec h).1
    next h => exact le_rfl
  have he: Tendsto (fun k=>g k (t k)) atTop (𝓝 (thinReadMatrix i j).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp
        (P.thin_direct_table x c r F U C p q f u t (Eventually.of_forall ht)) i) j)
  filter_upwards [he.eventually (lt_mem_nhds (half_lt_self (thin_positive_entry i j)))] with k v t' h
  by_contra! r
  let w: ∃ t≥c k,g k t ≤ K₀:= ⟨t',h,r⟩
  change K₀ < g k (t k) at v
  exact v.not_ge ((by rw [show t k=Nat.find w by unfold t; rw [dif_pos w]]; exact (Nat.find_spec w).2) : g k (t k)≤ K₀)

lemma thin_boxes (Z W:Lead.Clan) :
    ∀ᶠ i in atTop, P.spacePrice (((A i) Z).kiss P 3) F ⊆ x₋ ∧
                  P.spacePrice ((A i) W) U ⊆ x₊ :=
  (P.thin_inside (fun i=> (((A i) Z).kiss P 3)) (limit_width C.launch) x₋ (Doorway.doorOpen X₋) F p).and
    (P.thin_inside (fun i=>(A i) W) (limit_width C.launch) x₊ (Doorway.doorOpen X₊) U q)

omit C p q
structure ThinFixedLab (P:Spine)(x:P.Spectrum0 3)(c r:ℕ→ℕ)(F U: SampleDose) : Prop where
  earlier : tsupport F.val ⊆ x₋
  laterTest : tsupport U.val ⊆ x₊
  norm : F.Normalized ∧ U.Normalized
  seam (Z W:Lead.Clan) : P.ThinPair x F U (fun i=> P.thinMat Z (c i) (r i)) (fun i=> P.thinMat W (c i) (r i))
                         (P.thin_mat_born Z c r) (P.thin_mat_born W c r) z[Z] z[W]
  tryOld (Z W:Lead.Clan) : P.ThinPair x F U (fun i=> P.experimentBody Z (c i) (r i))
     (fun i=> P.experimentBody W (c i) (r i)) (fun i=>P.body_birth Z (c i) (r i)) (fun i=>P.body_birth W (c i) (r i)) 0 0
  insideBoxes : ∀ᶠ i in atTop,∀ Z:Lead.Clan, P.spacePrice ((P.thinMat Z (c i) (r i)).kiss P 3) F ⊆ x₋ ∧
                  P.spacePrice (P.thinMat Z (c i) (r i)) U ⊆ x₊
  actualVsSplit (t:ℕ→ℕ)(ht:∀ᶠ i in atTop, c i≤ t i) : Tendsto (fun i=>P.thinChargeMatrix x c r F U i (t i)) atTop (𝓝 thinReadMatrix)
  -- margin already financed at *every* mesh from the late purchase onward
  disparity : ∀ᶠ k in atTop, ∀ (i j:Lead.Clan)(t:ℕ), c k ≤ t →
       0 < (thinReadMatrix i j).re/2 ∧ (thinReadMatrix i j).re/2 < (P.thinChargeMatrix x c r F U k t i j).re

include C p q
lemma thin_front_charge (f:F.Normalized)(u:U.Normalized) : P.ThinFixedLab x c r F U := by
  have v:= narrowSide F U p q
  let X:=fun Z W : Lead.Clan=>P.thin_studies Z W c r x C F U 1 zero_lt_one v.1 v.2
  refine ⟨p,q,⟨f,u⟩,fun Z W=>(X Z W).1, fun Z W=>(X Z W).2,
    eventually_all.mpr (fun i=>P.thin_boxes x c r F U C p q i i), P.thin_direct_table x c r F U C p q f u,?_⟩
  refine eventually_all.mpr (fun i=>eventually_all.mpr (fun j=>?_))
  exact (coarse_criterion P x c r F U C p q f u i j).mono (fun k a t h=> ⟨half_pos (thin_positive_entry i j),a t h⟩)
omit C p q
end publishedLab
#print axioms thin_not_full_rank
#print axioms thin_kernel_far
#print axioms thin_regulator_formula
#print axioms thin_front_charge
section actual
-- make measurement on the *same* election; keep stronger Experiment
variable {K:P.Register}{c r:ℕ→ℕ}{x:P.Spectrum0 3}{J:P.Ellis 3 x}
local notation "X₋" => reviewEarlierBox
local notation "X₊" => reviewLaterBox

def thinAlongOrder : Orders := ⟨fun _=>true,rfl⟩
lemma thinEarlier : X₋.Later X₊ thinAlongOrder 0 := by
  intro j; norm_num [Doorway.Later, thinAlongOrder, reviewEarlierBox, reviewLaterBox]
lemma thin_separation (x y:Vantage)(e:x∈reviewEarlierBox.invites)(v:y∈reviewLaterBox.invites)(j:Axis) :
    x j + 2 < y j := by
  have hx:x j < -1:= (e j (Set.mem_univ _)).2; have hy:1 < y j:= (v j (Set.mem_univ _)).1
  linarith
lemma thin_receipt_applied (B:P.Experiment K c r x J): ∀ᶠ i:ℕ in atTop, ∃ (F U: SampleDose),
             (∀ m:Lead.Clan, P.spacePrice (P.RTest m (c i) (r i)) F ⊆ reviewEarlierBox.invites) ∧
             (∀ m:Lead.Clan, P.spacePrice (P.FTest m (c i) (r i)) U ⊆ reviewLaterBox.invites) ∧
             P.ReturnsSix x (c i) (r i) 0 F U ∧ P.FixedSatinReadings K x (c i) (r i) 0 F U ∧
             P.ThinFixedLab x c r F U := by
  let T':= trans6 B
  let b : Fin 3 → Bool := fun _=>false
  obtain ⟨y,δ,e,h,H⟩ := authorize b
  filter_upwards [packs_within_rectangles T' (Metric.ball y δ) b H _ _ thinAlongOrder thinEarlier,
                  (limit_width B.launch 3).eventually (gt_mem_nhds (show (0:ℝ)<1 from zero_lt_one)),
                  B.launch.eager.tendsto_atTop.eventually (eventually_gt_atTop P.calibration.ℓ)] with i p w v
  obtain ⟨a,F,U,hF,hU,hR,p,q,r₀,s₀⟩ := p.2
  let D:= narrowSide F U p q
  have hx:∀ Z, P.WallBefore (P.RTest Z (c i) (r i)) F 0:= by
    intro Z k hk; change k 3 + P.probeWidth (c i) (r i) 3 < 0
    linarith only [show P.probeWidth (c i) (r i) 3 < 1 from w, show k 3≤ -1 from D.1 k hk]
  have hy:∀ Z, P.WallAfter (P.FTest Z (c i) (r i)) U 0:=fun Z k hk=>
    (zero_add (P.probeWidth (c i) (r i) 3)).trans_lt ((show P.probeWidth (c i) (r i) 3<1 from w).trans_le (show (1:ℝ)≤ k 3 from D.2 k hk))
  have priceEq : P.arrayReading x (c i) (r i) 0 F U = P.arrayReading x (c i) (r i) a F U :=
    tendsto_nhds_unique (P.answersTogether x (c i) (r i) 0 J F U hx hy) hR.steady
  have he:P.ReturnsSix x (c i) (r i) 0 F U:= P.paidReturn x (c i) (r i) 0 F U hx hy J
        (priceEq.symm ▸ hR.poles) v
  exact ⟨F,U,r₀,s₀,he,P.reviewWardContrast K x (c i) (r i) _ F U he,P.thin_front_charge x c r F U B p q hF hU⟩

open Regis.Head Regis.Head.Brecht
/-- One physical supplied course, with a real purchase of the two-box experiment on one vacuum,
    then all the thin estimates in it. Includes exact `ReturnsSix` and
    `FixedSatinReadings` at the same test choices, as well as new, nonzero thin gauge-vs-matter
    discrepancies and the failure of a stronger propagated interpretation at this normalization.
    Use `ThinPair` for the vacuum order-one and order-two field statement, and
    `thin_comparator_LocalFieldBounds` and `thin_split_is_raw` for exact notion of factorization. -/
theorem thin_satin_front_lab (Y:Supplier)(L M:ℝ)(h:0<M)(w:ℕ→ℕ) :
    ∃ (P:Spine)(K:P.Register),uniform P K Y L M ∧ ∃ (c r: ℕ→ℕ)(x:P.Spectrum0 3)(J:P.Ellis 3 x), w ≤ r ∧
       P.Experiment K c r x J ∧ ∃ (i:ℕ)(F U:SampleDose),
             (∀ m:Lead.Clan, P.spacePrice (P.RTest m (c i) (r i)) F ⊆ reviewEarlierBox.invites) ∧
             (∀ m:Lead.Clan, P.spacePrice (P.FTest m (c i) (r i)) U ⊆ reviewLaterBox.invites) ∧
             P.ReturnsSix x (c i) (r i) 0 F U ∧ P.FixedSatinReadings K x (c i) (r i) 0 F U ∧
             P.ThinFixedLab x c r F U := by
  obtain ⟨P,K,e,c,r,x,t,J,B,_⟩ := macroscopicSatin Y L M h w
  exact ⟨P,K,e,c,r,x,J,t,B, (P.thin_receipt_applied B).exists⟩

/-- No hypotheses. See also `thin_kernel_far` for the point-price test
    on the same stamps at all physical positive-time gaps. -/
theorem thin_front_concrete :
    let Y:Supplier:= fun _ _ _ _ _ _ _ _ _ _ _ _ => 0
    ∃ (P:Spine)(K:P.Register),uniform P K Y 1 1 ∧ ∃ (c r: ℕ→ℕ)(x:P.Spectrum0 3)(J:P.Ellis 3 x), id ≤ r ∧
       P.Experiment K c r x J ∧ ∃ (i:ℕ)(F U:SampleDose),
             (∀ m:Lead.Clan, P.spacePrice (P.RTest m (c i) (r i)) F ⊆ reviewEarlierBox.invites) ∧
             (∀ m:Lead.Clan, P.spacePrice (P.FTest m (c i) (r i)) U ⊆ reviewLaterBox.invites) ∧
             P.ReturnsSix x (c i) (r i) 0 F U ∧ P.FixedSatinReadings K x (c i) (r i) 0 F U ∧
             P.ThinFixedLab x c r F U := thin_satin_front_lab _ 1 1 zero_lt_one id
end actual
#print axioms thin_front_concrete
#print axioms thin_satin_front_lab
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

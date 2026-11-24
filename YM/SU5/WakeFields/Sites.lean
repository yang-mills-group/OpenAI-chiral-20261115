import YM.SU5.WakeFields.PhysicalHistory


set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option maxRecDepth 2500
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Filter
open Function
open Metric
open MeasureTheory
open Lattice Cube Lat Skye Lifted EmberWind
open Py Py.Rate LocalLimit FullBill Preparation Yoke Journey
open Satin Fock
open Ballad
open scoped Topology BigOperators Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Onyx (riseX)
open YM.Stationary (Gaia)

namespace Resolving

open Finset
open EmberWind.Staff
open CF.Pannier.Chancel
open Signal.Interval (separationCost)
open Tapestry

/-- Staff at gauge site of the local Spin pair, adjacent oriented positive plaquette. -/
def adjacent (u : Cover) (F : PlaqAxes) (L : Twah.DirSpin) : Staff :=
  { hub := nodeC u, u := u, face := (nodeC u,F), spin := L, steps := [], stop_at := rfl }

private lemma visa4 (p : Face ℤ) : visa p ⊆ skyDeck p.1 4 := by
  unfold visa; generalize hA : Lattice.square p.2.val.1 p.2.val.2 = A
  have h : A.length = 4 := by rw [←hA]; rfl
  rw [←h]; exact fun x hx => walk_pav p.1 x A (List.mem_toFinset.mp hx)

lemma compRoom (u : Cover) (F : PlaqAxes) (L : Twah.DirSpin) {r w} (p : 4 ≤ r) :
    (adjacent u F L).Pays r w := by
  refine ⟨Nat.zero_le _,?_,?_⟩
  · intro x h; have he : x=nodeC u := List.mem_singleton.mp (show x ∈ [nodeC u] from h)
    rw [he]; exact owns _ _
  · change visa (nodeC u,F) ⊆ skyDeck (nodeC u) r
    exact (visa4 (nodeC u,F)).trans (pav_mono p)

-- metric-independent helpers
lemma offsetDeck (x y : Cover) {r s} (h : x ∈ skyDeck y r) :
    skyDeck x s ⊆ skyDeck y (r+s) := by
  intro z v; apply (pav_v ..).mpr
  intro a; obtain ⟨w,b⟩ := (pav_v ..).mp h a; obtain ⟨u,g⟩ := (pav_v ..).mp v a; omega

lemma nearTenancy (U : Staff) {x : Cover} {B : ℕ} (g : U.hub ∈ skyDeck x B)
    (n : Side) (r : ℕ) :
    U.tenancy n r Staff.clearance (B+(r+Staff.clearance+8)) (wrap (More n) x) := by
  rw [Staff.tenancy,gateS,←wrap_pav,BlockP,←wrap_pav]; exact image_subset_image (offsetDeck _ _ g)

lemma riseAdd (x : ℝ) (u v : Cover) : riseX x (u + v)=riseX x u + riseX x v := by
  ext j
  simp [Onyx.riseX, Onyx.moor, add_div]

lemma riseSub (x : ℝ) (u v : Cover) : riseX x (u - v)=riseX x u - riseX x v := by
  ext j; simp [Onyx.riseX, Onyx.moor, sub_div]

variable (P : Spine)
variable {A I : ℝ} {a b : Gaia} {u v : ℕ → Cover}
local notation "R_" s:max => sPow P.par s A
local notation "κ" => P.par.R.L
local notation "X_" s:max => Vale.hat P.par.R.L P.par.x s
open scoped NNReal

lemma axisBounds {x : Cover} {R b : ℝ} (p : 0 < R) (h : ‖riseX R x‖ ≤ b) (j : Axis) :
    |(x j:ℝ)| ≤ R * b := by
  have ht : |(x j:ℝ)/R| ≤ b := (PiLp.norm_apply_le (riseX R x) j).trans h
  rw [abs_div,abs_of_pos p,div_le_iff₀ p] at ht; rwa [mul_comm]

lemma bumped (b : ℝ) :
    ∀ᶠ s : ℕ in atTop, ∀ x : Cover, ‖riseX (R_ s) x‖ ≤ b → x ∈ skyDeck 0 ⌈(R_ s)*b⌉₊ := by
  apply Filter.Eventually.of_forall; intro s x h
  apply (pav_v ..).mpr; intro j
  let r := ⌈(R_ s)*b⌉₊
  have Q : |x j| ≤ (r:ℤ) := by
    exact_mod_cast le_trans (axisBounds (BProof.coin_pos ..) h j) (Nat.le_ceil ((R_ s)*b))
  have he := abs_le.mp Q; simp only [Pi.zero_apply,zero_add,zero_sub]; exact he

lemma payBump (b : ℝ) (m : ℕ) (t : 0 ≤ b) (g : A < I) (p : 0 < I) :
    ∀ᶠ s : ℕ in atTop, ((⌈(R_ s)*b⌉₊ + m : ℕ) : ℝ) ≤ sPow P.par s I := by
  open BProof in
  filter_upwards [grow_e I (2*(m+1)) p P.par,(turnover P.par).eventually
        (coin_budget (a:=0) (d:=0) (c:=0) (f:=0) (Or.inr (Or.inl ⟨rfl,g⟩)) (2*b) 1 zero_lt_one)] with s h f
  rw [one_mul] at f
  push_cast
  have hQ := Nat.ceil_lt_add_one (mul_nonneg (BProof.coin_pos (X_ s) 0 A 0).le t)
  unfold sPow at *; linarith only [h,f,hQ]

lemma fuel_hubs {U V : Staff} {r w} (p : U.Pays r w) (q : V.Pays r w) (x : Cover) (s B : ℕ)
    (f : U.hub ∈ skyDeck x B) (g : V.hub ∈ skyDeck x B) (t : (B+(r+Staff.clearance+8):ℕ) ≤ sPow P.par s I)
    (u : (w:ℝ) ≤ sPow P.par s I) : ∀ n : Side, PaidPair P I r s U V n :=
  fun n => ⟨_, w, wrap (More n) x,p,q, nearTenancy U f n r, nearTenancy V g n r, t,u⟩


lemma payRegion (b : ℝ) (t : 0 ≤ b) (p : A < I) (q : 0 < I) (r w : ℕ) :
    ∀ᶠ s : ℕ in atTop, ∀ U V : Staff, U.Pays r w → V.Pays r w →
      ‖riseX (R_ s) U.hub‖ ≤ b → ‖riseX (R_ s) V.hub‖ ≤ b →
        ∀ n : Side, PaidPair P I r s U V n := by
  filter_upwards [payBump P b (r+Staff.clearance+8) t p q, grow_e I w q P.par,
    bumped (A:=A) P b] with s v h H U V p q z y
  exact fuel_hubs P p q 0 s _ (H _ z) (H _ y) v h

abbrev roster (U : ℕ → Cover) (F : PlaqAxes) (L : Twah.DirSpin) : ℕ → Staff :=
  fun s => adjacent (U s) F L

variable (F G : PlaqAxes) (L D : Twah.DirSpin) (r : ℕ)

lemma paid (gs : 4 ≤ r) (p : 0 < A) (q : A < I) (F G : PlaqAxes) (L D : Twah.DirSpin)
    (U : Appoint P.par A u a) (V : Appoint P.par A v b) :
    ∀ᶠ s : ℕ in atTop, ∀ n : Side, PaidPair P I r s (roster u F L s) (roster v G D s) n := by
  let B := max ‖a‖ ‖b‖ + 1
  have hp : ‖a‖ < B := lt_of_le_of_lt (le_max_left ..) (lt_add_one _)
  have hq : ‖b‖ < B := lt_of_le_of_lt (le_max_right ..) (lt_add_one _)
  unfold Appoint at U V
  filter_upwards [payRegion P B ((norm_nonneg _).trans hp.le) q (p.trans q) r 0,
    U.norm.eventually (ge_mem_nhds hp), V.norm.eventually (ge_mem_nhds hq)] with s Q H J
  exact Q _ _ (compRoom _ _ _ gs) (compRoom _ _ _ gs) H J

/-- The two **actual** normalized force-ingredient Marks for this chapter are stamped
at matter coordinates `u`. They are *both mixed*. Later they'll need to be recognized
by pure-gauge and matter readings; their own nonzero Gram is not an interaction proof. -/
abbrev probe (β : ℕ → ℝ) (A : ℝ) (s : ℕ) (u : Cover) (F : PlaqAxes) (L : Twah.DirSpin) (r : ℕ) :
    Family P.calibration := operand P β A s (adjacent u F L) r

abbrev stencils (β : ℕ → ℝ) (A : ℝ) (u : ℕ → Cover) (F : PlaqAxes) (L : Twah.DirSpin) (r : ℕ) : ℕ → Family P.calibration :=
  fun s => probe P β A s (u s) F L r

lemma usable (β : ℕ → ℝ) (A : ℝ) (u : Cover) (h : 4 ≤ r) (s : ℕ) :
    InTest P.calibration true (skyDeck (nodeC u) (r+8)) false (probe P β A s u F L r) ∧
    CovCover P.calibration (probe P β A s u F L r) :=
  operand_admitted P β s _ 0 _ (compRoom u F L h) A

lemma cashAdj (f β) (h : Tuned P f β) (p : P.PhysicalWakeGram) (H : 0 < A) (q : 4 ≤ r)
    (U : Appoint P.par A u a) (V : Appoint P.par A v b) (he : a ≠ b) :
    MeanShot P f (stencils P β A u F L r) 0 ∧
    MeanShot P f (stencils P β A v G D r) 0 ∧
    MeanShot P f (stencils P β A u F L r * stencils P β A v G D r) (shot F G L D a b (a-b)) := by
  refine mixedWakeEstimate P (roster u F L) (roster v G D) F G L D f (show 0<A+1 by linarith) p h
    (fun _ => r) ((towerLate _).2 ?_) H (.of_forall fun _=>rfl) (.of_forall fun _=>rfl)
    (.of_forall fun _=>rfl) (.of_forall fun _=>rfl) U V he ?_ (sub_ne_zero.mpr he)
  · exact (paid P r q H (lt_add_one A) F G L D U V).mono fun s h =>
      .of_forall fun _ => h _
  unfold Appoint at *
  exact (U.sub V).congr fun s => (riseSub ..).symm

open Selected (gaugeMesh gaugeMesh_pos gaugePosition physical_shield)
-- scaled mortgage on the *true* physical ruler (matter units at level zero)

def apertureScale (A : ℝ) (s : ℕ) := sPow P.par s A * gaugeMesh P.par s
lemma apert_pos (s A) : 0 < apertureScale P A s := mul_pos (BProof.coin_pos ..) (gaugeMesh_pos ..)

lemma aperture_shrinks (A : ℝ) : Tendsto (apertureScale P A) atTop (𝓝 0) := by
  let L := (P.par.R.L.val:ℝ)
  have h : 1 < L := by simpa only [L,Nat.cast_one] using (Nat.cast_lt (α:=ℝ)).mpr (show 1 < P.par.R.L.val by have := P.par.V.tallX; omega)
  let f := fun s : ℕ => (1:ℝ) / L^s
  let g := fun s : ℕ => (s:ℝ) / L^s
  have hf : Tendsto f atTop (𝓝 0) := by simpa only [pow_zero] using tendsto_pow_const_div_const_pow_of_one_lt 0 h
  have hg : Tendsto g atTop (𝓝 0) := by simpa only [pow_one] using tendsto_pow_const_div_const_pow_of_one_lt 1 h
  have hu : Tendsto (fun s => (X_ s) * gaugeMesh P.par s) atTop (𝓝 0) := by
    have hp := ((hf.const_mul P.par.x).add (hg.const_mul (Vale.billX P.par.R.L))).div_const 2
    rw [mul_zero,mul_zero,add_zero,zero_div] at hp; apply hp.congr
    intro s; unfold Vale.hat f g L Selected.gaugeMesh; ring_nf
  apply squeeze_zero' (.of_forall (fun i => (apert_pos ..).le)) _ hu
  filter_upwards [(turnover P.par).eventually (BProof.coin_budget (a:=0) (b:=A) (c:=0) (d:=1) (e:=0) (f:=0) (Or.inl zero_lt_one) 1 1 zero_lt_one),
    (turnover P.par).eventually_gt_atTop 0] with s h₁ h₂
  rw [one_mul,one_mul,BProof.coinY h₂] at h₁
  exact mul_le_mul_of_nonneg_right h₁.le (gaugeMesh_pos ..).le

-- Actual tenancy obstruction to *direct* pairing/simultaneous sails with these budgets
-- at macroscopic distance. Allows all supported Staff heights.
open CF.Lamour.Bridge.Celeste (liftMoney)
lemma rentBound (U V : Staff) (I : ℝ) (s : ℕ) (r : ℕ) :
    ∀ᶠ n : Side in atTop, PaidPair P I r s U V n →
      (separationCost U.xo V.xo:ℝ) ≤ 2*sPow P.par s I := by
  filter_upwards [liftMoney {U.xo,V.xo}] with n H Hv
  obtain ⟨e,w,o,h,u,t,v,a,-⟩ := Hv
  specialize H _ (mem_insert_self ..) _ (mem_insert_of_mem (mem_singleton_self _))
  have g (U : Staff) (p : U.Pays r w) (u : U.tenancy n r Staff.clearance e o) :
      separation o (U.scope n) ≤ e := blocks_test.mp (u (Corona.halo_mono (show r ≤ r+Staff.clearance+8 by omega) (Subset.refl _) ((p.withinP U n).2.1)))
  have he := g U h t; have hz := g V u v
  have hg := separation_triangle (U.scope n) o (V.scope n); rw [separation_comm _ o] at hg
  have hk : separationCost U.xo V.xo ≤ e+e := H.symm.trans_le (hg.trans (add_le_add he hz))
  apply le_trans (Nat.cast_le.mpr hk); push_cast; linarith

lemma axisCharge (P : Spine) (t : ℕ) (x y : Cover) (j : Axis) :
    |gaugePosition P.par t x j-gaugePosition P.par t y j| ≤
        (separationCost x y:ℝ) * gaugeMesh P.par t := by
  have hz : |x j-y j| ≤ (separationCost x y:ℤ) := by
    rw [←Int.natCast_natAbs]; exact_mod_cast (Finset.le_sup (f:=fun i => ((x-y) i).natAbs) (Finset.mem_univ j))
  rw [Selected.gaugePosition,Selected.gaugePosition,←_root_.sub_mul,abs_mul,abs_of_pos (gaugeMesh_pos ..)]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hz) (gaugeMesh_pos ..).le

/-- Every paid pair (even non-adjacent Staff) at those s-placements, on the
   coherent period progression, has Spin inserts separated only microscopically.
   A fixed physical reading will need progression in **other** prices, not costing
   that pair by `GramPace.duo` at the travelling resolution forever. -/
theorem staff_obstruction (I : ℝ) (U V : ℕ → Staff) (f : ℕ → ℕ) (hf : StrictMono f)
    (r : ℕ → ℕ)
    (h : ∀ᶠ i in towerLimit, PaidPair P I (r i.1) i.1 (U i.1) (V i.1) (side P.run (physicalPeriod P f i.2) i.1))
    (ε : ℝ) (e : 0 < ε) : ∀ᶠ s : ℕ in atTop, ∀ j : Axis,
       |gaugePosition P.par s (U s).xo j - gaugePosition P.par s (V s).xo j| ≤ ε := by
  rw [towerLate] at h
  filter_upwards [h, (aperture_shrinks P I).eventually (ge_mem_nhds (show 0<ε/2 by positivity))] with s h hv j
  let f' := (Papal.count_la P.run s).comp ((period_grows P f hf).tendsto_atTop)
  obtain ⟨n, l⟩ := (h.and (f'.eventually (rentBound P (U s) (V s) I s (r s)))).exists
  refine (axisCharge P s _ _ j).trans ((mul_le_mul_of_nonneg_right (l.2 l.1) (gaugeMesh_pos ..).le).trans ?_)
  rw [mul_assoc]; change 2 * apertureScale P I s ≤ _; linarith only [show apertureScale P I s ≤ ε/2 from hv]


open Tapestry Reconstruction

/-- inside a scaled-open-square (all four coordinates), with its physical reserve,
   uniformly on the indicated sites; the scale is *shrinking*. -/
def cellAt (a : Gaia) (d ε : ℝ) : Set RSpace :=
  {p | ∀ j : Axis, |p j - d * a j| < d*ε }

lemma stencilScale (A : ℝ) (s : ℕ) (x : Cover) (j : Axis) :
    gaugePosition P.par s x j = apertureScale P A s * riseX (sPow P.par s A) x j := by
  rw [apertureScale]
  have he : 0 < sPow P.par s A := BProof.coin_pos ..
  change _ * gaugeMesh P.par s = _ * ((x j:ℝ)/sPow P.par s A)
  field_simp

-- even all printed buffer included, no statement it's paying twist under a continuous rotation
lemma apartment {u : ℕ → Cover} (H : 0 < A) (g : Appoint P.par A u a)
    (ε : ℝ) (p : 0 < ε) (r : ℕ) : ∀ᶠ s in atTop,
      silhouette P.par P.width s (skyDeck (nodeC (u s)) r) ⊆ cellAt a (apertureScale P A s) ε := by
  unfold Appoint at g
  let m : ℕ := reserve P.par P.width
  let b := r+m
  let d (s) := apertureScale P A s
  filter_upwards [(sPower_pay P.par H).eventually_gt_atTop ((b:ℝ)/(ε/2)),
            (Metric.tendsto_nhds.mp g) (ε/2) (by positivity)] with s hx hr y qx
  obtain ⟨x,h,r'⟩ := silhouette_iff.mp qx
  intro a'
  let i := nodeC (u s)
  let T := gaugeMesh P.par s
  have ht : 0 < T := gaugeMesh_pos ..
  have hv : (b:ℝ) < (R_ s)*(ε/2) := (div_lt_iff₀ (half_pos p)).mp hx
  let R := gaugeRise P.par s A (u s)
  have he: |R a'-a a'| < ε/2 := (PiLp.norm_apply_le (R-a) a').trans_lt (dist_eq_norm R a ▸ hr)
  let z := riseX (R_ s) x
  have hy: |(x a':ℤ)-i a'| ≤ (r:ℤ) := by
    have hz := (pav_v ..).mp h a'; change i _ - _ ≤ _ ∧ _ ≤ i _+_ at hz
    rw [abs_le]; omega
  have hg: |gaugePosition P.par s x a'-gaugePosition P.par s i a'| ≤ (r:ℝ)*T := by
    rw [Selected.gaugePosition,Selected.gaugePosition,←_root_.sub_mul,abs_mul,abs_of_pos ht];
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hy) ht.le
  have hj := stamp_abs.mp r' a'
  have hk: (d s)*(ε/2) = (R_ s)*(ε/2)*T := by unfold d apertureScale; ring
  have hh: |gaugePosition P.par s i a' - (d s)*a a'| < (d s)*(ε/2) := by
    have e := apert_pos P s A
    rw [show gaugePosition P.par s i a'=d s*R a' from stencilScale P A s i a', ←mul_sub,abs_mul,abs_of_pos e]; exact mul_lt_mul_of_pos_left he e
  change _ ≤ (m:ℝ)*T at hj
  have hZ: |y a' - (d s)*a a'| ≤ |y a' -gaugePosition P.par s x a'|+|gaugePosition P.par s x a'-gaugePosition P.par s i a'|+|gaugePosition P.par s i a'-(d s)*a a'| := by
    exact (abs_sub_le _ (gaugePosition P.par s i a') _).trans (add_le_add (abs_sub_le ..) le_rfl)
  have hX := mul_lt_mul_of_pos_right hv ht
  unfold b at hX; push_cast at hX
  change _ < (d s)* ε
  linarith

-- link footprint relationship under further height advancement
lemma stamped_later (s n : ℕ) (Q : Set RSpace) {S : Finset Cover} (h : silhouette P.par P.width s S ⊆ Q) :
    silhouette P.par P.width (s+n) (volumeAround P.par P.width n S) ⊆ Q := by
  rintro y u
  obtain ⟨x,hx,p⟩ := silhouette_iff.mp u
  obtain ⟨z,v,t⟩ := physical_shield P.par P.width s S n hx
  apply h; apply silhouette_iff.mpr; refine ⟨z,v,stamp_abs.mpr fun i=> ?_⟩
  specialize t i
  have hv := stamp_abs.mp p i
  exact (abs_sub_le _ (gaugePosition P.par (s+n) x i) _).trans (by linarith only [hv,t])

#print axioms apartment
#print axioms stamped_later
end Resolving
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

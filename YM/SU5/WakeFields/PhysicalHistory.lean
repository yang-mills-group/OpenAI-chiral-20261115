import SU5SatinWakePhysicalGramNovember8

/-!
# Resolving the physical Wake Gram

`towerLimit` below will always charge `n` (period/cutoff) late **after** `s` (resolution) — not limit on product filter.
-/

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

def towerLimit : Filter (ℕ × ℕ) :=
  Filter.bind atTop fun s => Filter.map (fun n => (s,n)) atTop

theorem towerLate (p : ℕ × ℕ → Prop) : (∀ᶠ i in towerLimit, p i) ↔
    ∀ᶠ s : ℕ in atTop, ∀ᶠ n : ℕ in atTop, p (s,n) := Iff.rfl

theorem firstTends : Tendsto Prod.fst towerLimit atTop := by
  rw [Filter.tendsto_atTop]
  intro s
  rw [towerLate]; exact (eventually_ge_atTop s).mono fun _ h => .of_forall fun _ => h

instance : NeBot towerLimit := ⟨by
  intro h
  have : ∀ᶠ i in towerLimit, False := by simp [h]
  rw [towerLate] at this
  exact this.exists.elim fun _ p => p.exists.elim fun _ q => q⟩

-- collapse first at each s into the same L-limit
lemma passage {E : Type*} [PseudoMetricSpace E] {x : ℕ × ℕ → E} {y : ℕ → E} {z : E}
    (h : Tendsto x towerLimit (𝓝 z))
    (g : ∀ᶠ s in atTop, Tendsto (fun n : ℕ => x (s,n)) atTop (𝓝 (y s))) :
    Tendsto y atTop (𝓝 z) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hz := Metric.tendsto_nhds.mp h (ε/2) (by positivity)
  rw [towerLate] at hz
  filter_upwards [hz, g] with s H G
  apply lt_of_le_of_lt _ (half_lt_self hε)
  exact le_of_tendsto (G.dist (tendsto_const_nhds (x := z))) (H.mono fun _ v => v.le)

open Jewel
open Regis Regis.Head Regis.Circuit Regis.Head.Brecht
open EmberWind
open Scree

/-- `f` is a subsequence on the already coherent physical progression. -/
abbrev physicalPeriod (P : Spine) (f : ℕ → ℕ) : ℕ → ℕ :=
  (P.period ∘ P.projection.rows) ∘ f
abbrev physicalCut (P : Spine) (f : ℕ → ℕ) : ℕ → ℕ :=
  (P.cutoff ∘ P.projection.columns) ∘ f

def Tuned (P : Spine) (f : ℕ → ℕ) (β : ℕ → ℝ) : Prop :=
  Jewel.Pooling P.run (P.period ∘ P.projection.rows) (P.cutoff ∘ P.projection.columns) f β

theorem tuneFurther (P : Spine) {f : ℕ → ℕ} (h : StrictMono f) :
    ∃ c : ℕ → ℕ, ∃ β, StrictMono c ∧ Tuned P (f ∘ c) β :=
  Pooling.fettle P.run P.history h

variable (P : Spine)

variable {A : ℝ} {a b : Gaia} {β : ℕ → ℝ} (U V : ℕ → Staff)
variable (F G : PlaqAxes) (L D : Twah.DirSpin)
variable (f : ℕ → ℕ)

local notation "Y" => P.run
local notation "ι" => physicalPeriod P f
local notation "k" => physicalCut P f
local notation "R_" s:max => sPow P.par s A
local notation "r_" s:max => zoomR P.par A s

section
include P

lemma zoom_pos (A : ℝ) (s : ℕ) : 0 < zoomR P.par A s := by
  apply Nat.ceil_pos.mpr
  exact half_pos (BProof.coin_pos ..)

end

lemma allotment (w : ℝ) (hw : w < 0) (A : ℝ) (m : ℕ) : Tendsto
    (fun s : ℕ => sPow P.par s A ^ m * WakeInvestment.chip (Vale.hat P.par.R.L P.par.x s) w)
    atTop (𝓝 0) := by
  have hneg : w / 400000 < 0 := div_neg_of_neg_of_pos hw (by norm_num)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(turnover P.par).eventually (BProof.coin_budget (a:=w/400000) (b:=A*m) (d:=0)
                      (c:=0) (e:=0) (f:=0) (Or.inl hneg) 1 ε hε)] with s h
  rw [dist_zero_right, Real.norm_of_nonneg]; swap
  · exact mul_nonneg (pow_nonneg (BProof.coin_pos ..).le _) (BProof.coin_pos ..).le
  simpa only [sPow, WakeInvestment.chip, BProof.coin_pow,BProof.coin_mul,zero_mul,zero_add,add_zero,
    BProof.coin_zero,mul_one,one_mul] using h

-- keep both s and n visible in public statement via iterated filter.
lemma gatheringOnTower (u : Tuned P f β) :
    Tendsto (fun i : ℕ × ℕ =>
      reachCost Y i.1 (ι i.2) (k i.2) (κFix β i.1)) towerLimit (𝓝 1) := by
  refine tendsto_def.mpr fun s h => (towerLate _).2 (.of_forall fun z => ?_)
  exact ((Gathering Y u z).eventually (show ∀ᶠ i : ℝ in 𝓝 1, i ∈ s from h))

-- keep denominator qualifications simultaneous

lemma pathPaidFixed (s : ℕ) (hf : StrictMono f) :
    ∀ᶠ n : ℕ in atTop, Ferry Y s (ι n) (k n) :=
  hf.tendsto_atTop.eventually (P.history.finance s)

/-- The actual denominator (not the solder price). Using `Papal.gram, room` wrappers
on `Preparation` keeps elaboration under control. -/
abbrev denominator {P : Preparation} {l : ℕ} (X : P.Course (VolumeCape.Dream.Nimbus l)) (s i n : ℕ) : ℂ :=
  partitionZ (Papal.gram X s i n) P.U (Papal.room X s i)

lemma rent (K : P.Register) (E : ℝ) (Mc : ℕ) (h : Spine.PreparedInvestment P K E Mc)
    (hf : StrictMono f) : ∀ᶠ i in towerLimit,
    Ferry Y i.1 (ι i.2) (k i.2) ∧
    ShelterRent Y i.1 (ι i.2) (k i.2) ∧
    denominator P.run i.1 (ι i.2) (k i.2) ≠ 0 := by
  rw [towerLate]; filter_upwards [rents Y h.rocky.merit] with s z
  filter_upwards [pathPaidFixed P f s hf] with n w
  exact ⟨w, z _ _ w.depth w.enters, Papal.part_here Y (ι n) s (k n) w⟩


lemma period_grows (hf : StrictMono f) : StrictMono (physicalPeriod P f) :=
  (P.law.pick.grow_i.comp P.history.growsA).comp hf

lemma spin_rescale (U V : Staff) (s i j r : ℕ) : (r:ℂ)^6 *
    spinCoupon Y s i j U V = Hiro.diced r U.u V.u U.spin V.spin
        (side Y i s) P.par.K.j (RootBook Y i j s).J.M := by
  unfold spinCoupon Hiro.diced Hiro.dietary
  simp_rw [Hiro.in_transcript, Emu.hopF]
  push_cast
  ring

lemma spin_limit (hf : StrictMono f) (p : 0 < A)
    (hL : ∀ᶠ s in atTop, (U s).spin = L)
    (hD : ∀ᶠ s in atTop, (V s).spin = D)
    (u : Appoint P.par A (fun s => (U s).u) a)
    (v : Appoint P.par A (fun s => (V s).u) b)
    (e : a ≠ b) :
    Tendsto (fun i : ℕ × ℕ =>
      (zoomR P.par A i.1 : ℂ)^6 * spinCoupon Y i.1 (ι i.2) (k i.2) (U i.1) (V i.1)) towerLimit
          (𝓝 (Hiro.shotR L D (X := a-b))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε g
  let r := zoomR P.par A
  let a' s := (U s).u
  let b' s := (V s).u
  have w : Tendsto (fun s => riseX (r s) (a' s - b' s)) atTop (𝓝 (a-b)) := by
    refine (((appoint_as P.par p _ a).1 u).sub ((appoint_as P.par p _ b).1 v)).congr fun s => ?_
    ext j
    simp [Onyx.riseX, Onyx.moor, a', b', r, sub_div]
  rw [towerLate]; filter_upwards [Hiro.travel_feast P.par.K.j L D (nontrivial_spin P.par) r
                       (zoom_grows P.par p) (zoom_pos P A) b' a' w (sub_ne_zero.mpr e) (ε/2) (by positivity),
                      hL,hD] with s h hL hD
  filter_upwards [((Papal.count_la Y s).comp ((period_grows P f hf).tendsto_atTop)).eventually h]
                    with n h
  change dist ((r s:ℂ)^6 * spinCoupon Y s (ι n) (k n) (U s) (V s)) _ < ε
  rw [spin_rescale,hL,hD]
  exact (h (Vale.val_e ..) _).trans_lt (half_lt_self g)

lemma magnify_coupon (U V : Staff) (r : ℝ) (n : Side) (M : Precision.Bed) :
    (r:ℂ)^4 * gaugeCoupon U V n M = acePower SU.group
      (magnify M r (Exterior.plaquette U.face.2) (Exterior.plaquette V.face.2)
                   (U.face.1 - V.face.1) (More n)) := by
  let R := More n
  let u := U.face.1
  let v := V.face.1
  let F := Exterior.plaquette U.face.2
  let D := Exterior.plaquette V.face.2
  have h : magnify M r F D (u-v) R = (r:ℂ)^4*rimble R M (wrap R u,F) (wrap R v,D) := by
    unfold magnify
    rw [rimflare R M (wrap R u) (wrap R v) (u-v) (map_sub (wrap R) u v).symm,
        rimflare R M (wrap R (u-v)) 0 (u-v) (sub_zero _)]
  rw [h]; unfold acePower gaugeCoupon
  dsimp only [u,v,F,D,R]; ring

-- may offset faces at mesh, only need their own pair cost at the same gauge-spacing ruler R
lemma gauge_limit (hf : StrictMono f) (p : 0 < A)
    (hF : ∀ᶠ s in atTop, (U s).face.2 = F) (hG : ∀ᶠ s in atTop, (V s).face.2 = G)
    {z : Gaia}
    (hpos : Tendsto (fun s => riseX (sPow P.par s A) ((U s).face.1-(V s).face.1)) atTop (𝓝 z))
    (ha : z ≠ 0) :
    Tendsto (fun i : ℕ × ℕ => (sPow P.par i.1 A:ℂ)^4 * gaugeCoupon (U i.1) (V i.1)
                          (side Y (ι i.2) i.1) (P.par.V.L.H (P.run.uv (k i.2) - i.1)))
            towerLimit (𝓝 (speckleV F G SU.group z)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε g
  rw [towerLate]; filter_upwards [manifold F G P.par.K.top.clip (P.par.V.W.parcel) P.par.K.width
        (zero_lt_one.trans_le P.par.V.up) (fun s => BProof.coin_pos ..) (sPower_pay P.par p)
        (U:=fun s=>(U s).face.1) (W:=fun s=>(V s).face.1) hpos ha (ε/2) (by positivity) SU.group,
        hF,hG] with s h hF hG
  filter_upwards [((Papal.count_la Y s).comp ((period_grows P f hf).tendsto_atTop)).eventually h] with n h
  let i := ι n; let x := P.run.uv (k n) - s
  let M := P.par.V.L.H x; let N := side Y i s
  change dist ((sPow P.par s A:ℂ)^4 * gaugeCoupon (U s) (V s) N M) _ < ε
  rw [magnify_coupon,hF,hG]
  have hx := P.par.V.L.roof x
  exact (h M hx.1 (hx.2.1 _)).trans_lt (half_lt_self g)


/- Obtain physical `P.E` values after two such licensed limits. Reader includes the
R_s^5 power; consumption of `β'` amplitude is at this particular held height. -/

def operand (P : Spine) (β : ℕ → ℝ) (A : ℝ) (s : ℕ) (U : Staff) (r : ℕ) :
    Family P.calibration :=
  (sPow P.par s A : ℂ)^5 • Papal.household P.calibration
    (U.rungWeave (κFix β s) r (Pressure.temp (Vale.hat P.par.R.L P.par.x s)))

lemma operand_admitted (β) (s r w) (U : Staff) (u : U.Pays r w) (A) :
    InTest P.calibration true (U.skyRent r) false (operand P β A s U r) ∧
    CovCover P.calibration (operand P β A s U r) :=
  ⟨.smul _ (Staff.letterBudget U (κFix β s) _ _ u),
    covariant_scale _ (Staff.registration U _ _ _ u) _⟩

local notation "θ_" s:max => Pressure.temp (Vale.hat P.par.R.L P.par.x s)

lemma readSingle (β : ℕ → ℝ) (A : ℝ) (s i j r : ℕ) (U : Staff) :
    sharp Y P.large s i j (operand P β A s U r) =
      ((sPow P.par s A:ℂ)^5) * compass Y i j s (U.rungWeave (κFix β s) r (θ_ s) (side Y i s)) := by
  rw [operand,sharp_scale]
  let a := U.rungWeave (κFix β s) r (θ_ s)
  change _* compass Y i j s (expSrc Y s i P.large (Papal.household P.calibration a)) = _
  rw [lift_book]

lemma readDuo (β : ℕ → ℝ) (A : ℝ) (s i j r : ℕ) (U V : Staff) :
    sharp Y P.large s i j (operand P β A s U r * operand P β A s V r) =
      ((sPow P.par s A:ℂ)^10) * compass Y i j s ((U.rungWeave (κFix β s) r (θ_ s) *
                         V.rungWeave (κFix β s) r (θ_ s)) (side Y i s)) := by
  rw [operand,operand,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,sharp_scale,sharp_scale]
  let a := U.rungWeave (κFix β s) r (θ_ s) * V.rungWeave (κFix β s) r (θ_ s)
  change _*(_ * compass Y i j s (expSrc Y s i P.large (Papal.household P.calibration a))) = _
  rw [lift_book,←mul_assoc, ←pow_add]

lemma unfray (s A) : (2*frayR P.par A s) * (zoomR P.par A s) = sPow P.par s A := by
  have p := zoom_pos P A s
  unfold frayR; field_simp

lemma wale_limit (p : 0 < A) (u : Tuned P f β)
    (hL : ∀ᶠ s in atTop, (U s).spin = L) (hD : ∀ᶠ s in atTop, (V s).spin = D)
    (hF : ∀ᶠ s in atTop, (U s).face.2 = F) (hG : ∀ᶠ s in atTop, (V s).face.2 = G)
    (hu : Appoint P.par A (fun s => (U s).u) a)
    (hv : Appoint P.par A (fun s => (V s).u) b)
    (e : a ≠ b) {z : Gaia}
    (hz : Tendsto (fun s => riseX (sPow P.par s A) ((U s).face.1-(V s).face.1)) atTop (𝓝 z))
    (ha : z ≠ 0) :
    Tendsto (fun i : ℕ × ℕ => ((sPow P.par i.1 A:ℂ)^10) *
                                wale Y i.1 (ι i.2) (k i.2) (U i.1) (V i.1) (κFix β i.1))
      towerLimit (𝓝 (2^6 * Hiro.shotR L D (X:=a-b) * speckleV F G SU.group z)) := by
  have HF : StrictMono f := Pooling.up u
  have he : Tendsto (fun i : ℕ × ℕ => (2* (frayR P.par A i.1:ℂ))^6) towerLimit (𝓝 (2^6)) := by
    have H : Tendsto (fun i : ℕ × ℕ => (frayR P.par A i.1:ℂ)) towerLimit (𝓝 ((1:ℝ):ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp ((fray_lift P.par p).comp firstTends)
    simpa only [Complex.ofReal_one,mul_one] using (H.const_mul (2:ℂ)).pow 6
  have hreach : Tendsto (fun i : ℕ × ℕ => (reachCost Y i.1 (ι i.2) (k i.2) (κFix β i.1):ℂ)^2) towerLimit
        (𝓝 1) := by
    have ht := Complex.continuous_ofReal.continuousAt.tendsto.comp (gatheringOnTower P f u)
    simpa only [comp_def,Complex.ofReal_one,one_pow] using ht.pow 2
  have h := ((he.mul (spin_limit P U V L D f HF p hL hD hu hv e)).mul
                   (gauge_limit P U V F G f HF p hF hG hz ha)).mul hreach
  rw [mul_one] at h; apply h.congr
  rintro ⟨s,n⟩; let a := ι n; let b := k n
  let X : ℂ := R_ s
  let c : ℂ := r_ s
  let B := spinCoupon Y s a b (U s) (V s)
  let C : ℂ := reachCost Y s a b (κFix β s)
  let W := gaugeCoupon (U s) (V s) (side Y a s) (P.par.V.L.H (P.run.uv b - s))
  let S := (2* (frayR P.par A s:ℂ))
  have hf : S*c=X := by unfold S c X; exact_mod_cast unfray P s A
  change S^6 * (c^6 * B) * (X^4 * W) * C^2 = X^10*(B*C^2*W)
  rw [←hf]; ring


/-- The required *common* enclosing block for pairing. Width paid only up to a fixed
power of `scaleY`. This is microscope layout, not cover for a macroscopic rectangle. -/
def PaidPair (I : ℝ) (r s : ℕ) (U V : Staff) (n : Side) : Prop :=
  ∃ e w : ℕ, ∃ o : Seat n,
    U.Pays r w ∧ V.Pays r w ∧
    U.tenancy n r Staff.clearance e o ∧ V.tenancy n r Staff.clearance e o ∧
    (e:ℝ) ≤ sPow P.par s I ∧ (w:ℝ) ≤ sPow P.par s I

lemma paidSym {s I r n} {U V : Staff} (v : PaidPair P I r s U V n) : PaidPair P I r s V U n := by
  obtain ⟨e,w,o,h,u,z,b,Q⟩ := v; exact ⟨e,w,o,u,h,b,z,Q⟩

lemma passport {s I r n} {U V : Staff} (v : PaidPair P I r s U V n) (β A) :
    TestFamily P.calibration true (operand P β A s U r) := by
  obtain ⟨e,w,o,u,-⟩ := v; exact aux_test (operand_admitted P _ _ _ _ _ u _).1

lemma heightLate {I} (p : 0 < I) (u : P.PhysicalWakeGram) (g : StrictMono f) :
    ∀ᶠ i in towerLimit, GramPace Y i.1 (ι i.2) (k i.2) I :=
  (towerLate _).2 ((u I p).mono fun _ h => g.tendsto_atTop.eventually h)

abbrev scaledBill (A : ℝ) (m s : ℕ) :=
  sPow P.par s A ^ m * WakeInvestment.chip (Vale.hat P.par.R.L P.par.x s) (-3)

lemma billTends (A : ℝ) (m : ℕ) : Tendsto (fun i : ℕ × ℕ => scaledBill P A m i.1) towerLimit (𝓝 0) :=
  (allotment P (-3) (by norm_num) A m).comp firstTends

/-- Uniform finite-Compass fees for the normalized s-Dome observables. -/
theorem priced {I : ℝ} (c : 0 < I) (u : P.PhysicalWakeGram) (v : Tuned P f β)
    (A : ℝ) : ∀ᶠ i in towerLimit, ∀ (r : ℕ) (U V : Staff),
      PaidPair P I r i.1 U V (side Y (ι i.2) i.1) →
      let pay := sharp Y P.large i.1 (ι i.2) (k i.2)
      let X := operand P β A i.1 U r
      let Z := operand P β A i.1 V r
      ‖pay X‖ ≤ scaledBill P A 5 i.1 ∧ ‖pay Z‖ ≤ scaledBill P A 5 i.1 ∧
      ‖pay (X*Z) - (sPow P.par i.1 A:ℂ)^10 * wale Y i.1 (ι i.2) (k i.2) U V (κFix β i.1)‖ ≤
            scaledBill P A 10 i.1 := by
  filter_upwards [heightLate P f c u (Pooling.up v)] with ⟨s,n⟩ h
  intro r U V Hv pay X Z
  let m := ι n; let a := k n; let N := side Y m s
  obtain ⟨e,w,o,hU,hV,T,U',he,hw⟩ := Hv
  let κ := κFix β s
  have K : |κ| ≤ 2* bornQ P.par s := paidFix Y v P.large s
  have R (j : ℕ) : ‖(sPow P.par s A:ℂ)^j‖ = sPow P.par s A ^ j := by
    rw [norm_pow,Complex.norm_real,Real.norm_of_nonneg (BProof.coin_pos ..).le]
  have S (W : Staff) (y : W.Pays r w) (z : W.tenancy N r Staff.clearance e o) :
      ‖sharp Y P.large s m a (operand P β A s W r)‖ ≤ scaledBill P A 5 s := by
    rw [readSingle,norm_mul,R]
    exact mul_le_mul_of_nonneg_left (h.single y z K he hw) (pow_nonneg (BProof.coin_pos ..).le _)
  refine ⟨S U hU T,S V hV U',?_⟩
  change ‖sharp Y P.large s m a (operand P β A s U r * operand P β A s V r) - _‖ ≤ _
  rw [readDuo, ←mul_sub,norm_mul,R]
  exact mul_le_mul_of_nonneg_left (h.duo hU T hV U' K he hw) (pow_nonneg (BProof.coin_pos ..).le _)

abbrev shot (F G : PlaqAxes) (L D : Twah.DirSpin) (a b z : Gaia) :=
  2^6 * Hiro.shotR L D (X:=a-b) * speckleV F G SU.group z
/-- A moment on `P.E` *and* licensed finite-`n` refinement after `s`. -/
structure MeanShot (P : Spine) (f : ℕ → ℕ)
    (X : ℕ → Family P.calibration) (Z : ℂ) : Prop where
  registered : ∀ᶠ s in atTop, TestFamily P.calibration true (X s) ∧ CovCover P.calibration (X s)
  approved : Tendsto (fun i : ℕ × ℕ =>
                     sharp P.run P.large i.1 (physicalPeriod P f i.2) (physicalCut P f i.2) (X i.1)) towerLimit (𝓝 Z)
  realized : Tendsto (fun s => P.E s (X s)) atTop (𝓝 Z)

lemma mean_grant {X : ℕ → Family P.calibration} {Z : ℂ} (u : StrictMono f)
    (v : ∀ᶠ s in atTop, TestFamily P.calibration true (X s) ∧ CovCover P.calibration (X s))
    (h : Tendsto (fun i : ℕ × ℕ => sharp Y P.large i.1 (ι i.2) (k i.2) (X i.1)) towerLimit (𝓝 Z)) : MeanShot P f X Z :=
  ⟨v,h, passage h (v.mono fun s p => (sharp_on_track Y P.law P.history s p.1).comp u.tendsto_atTop)⟩

local notation "μ[" i ", " x "]" =>
  sharp P.run P.large (Prod.fst i) (physicalPeriod P f (Prod.snd i)) (physicalCut P f (Prod.snd i)) x

theorem mixedWakeEstimate {I : ℝ} (hI : 0 < I) (g : P.PhysicalWakeGram) (h : Tuned P f β)
    (r : ℕ → ℕ) (moved : ∀ᶠ i in towerLimit, PaidPair P I (r i.1) i.1 (U i.1) (V i.1) (side Y (ι i.2) i.1))
    (p : 0 < A)
    (hL : ∀ᶠ s in atTop, (U s).spin = L) (hD : ∀ᶠ s in atTop, (V s).spin = D)
    (hF : ∀ᶠ s in atTop, (U s).face.2 = F) (hG : ∀ᶠ s in atTop, (V s).face.2 = G)
    (hu : Appoint P.par A (fun s => (U s).u) a) (hv : Appoint P.par A (fun s => (V s).u) b)
    (e : a ≠ b) {z : Gaia}
    (hz : Tendsto (fun s => riseX (sPow P.par s A) ((U s).face.1-(V s).face.1)) atTop (𝓝 z))
    (ha : z ≠ 0) :
    let X := fun s => operand P β A s (U s) (r s)
    let Z := fun s => operand P β A s (V s) (r s)
    MeanShot P f X 0 ∧ MeanShot P f Z 0 ∧ MeanShot P f (X*Z) (shot F G L D a b z) := by
  intro X Z
  let E := shot F G L D a b z
  have pm := Pooling.up h
  have keep := ((priced P f hI g h A).and moved).mono
                    (fun i h => h.1 _ _ _ h.2)
  let S (x : ℕ → Family P.calibration) (i : ℕ × ℕ) := μ[i,x i.1]
  let P' (i : ℕ × ℕ) := (R_ i.1 : ℂ)^10 * wale Y i.1 (ι i.2) (k i.2) (U i.1) (V i.1) (κFix β i.1)
  have enter (x : ℕ × ℕ → ℂ) (n : ℕ) (v : ∀ᶠ i in towerLimit, ‖x i‖ ≤ scaledBill P A n i.1) :
      Tendsto x towerLimit (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero' (.of_forall fun _ => norm_nonneg _) v (billTends P A n)
  have single : Tendsto (S X) towerLimit (𝓝 0) := enter _ 5 (keep.mono fun _ h => h.1)
  have second : Tendsto (S Z) towerLimit (𝓝 0) := enter _ 5 (keep.mono fun _ h => h.2.1)
  have duo : Tendsto (fun i => S (X*Z) i-P' i) towerLimit (𝓝 0) :=
    enter _ 10 (keep.mono fun _ h => h.2.2)
  have W : Tendsto P' towerLimit (𝓝 E) := wale_limit P U V F G L D f p h hL hD hF hG hu hv e hz ha
  rw [towerLate] at moved
  have Q (B : ℕ → Staff) (v : ∀ᶠ s in atTop, ∃ w, (B s).Pays (r s) w) :
      ∀ᶠ s in atTop, let X := operand P β A s (B s) (r s)
                     TestFamily P.calibration true X ∧ CovCover P.calibration X := v.mono fun s p =>
        let h := operand_admitted P β s (r s) _ _ p.choose_spec A
        ⟨aux_test h.1,h.2⟩
  have XA := Q U (moved.mono fun s p => ⟨_,p.exists.choose_spec.choose_spec.choose_spec.choose_spec.1⟩)
  have XZ := Q V (moved.mono fun s p => ⟨_,p.exists.choose_spec.choose_spec.choose_spec.choose_spec.2.1⟩)
  refine ⟨mean_grant P f pm XA single,mean_grant P f pm XZ second,mean_grant P f pm ?_ ?_⟩
  · filter_upwards [XA, XZ] with s a b
    exact ⟨a.1.mul b.1,(covariant_parts _ a.2 b.2).2⟩
  have W':=duo.add W; rw [zero_add] at W'; exact W'.congr fun _ => sub_add_cancel ..
#print axioms mixedWakeEstimate
end Resolving
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

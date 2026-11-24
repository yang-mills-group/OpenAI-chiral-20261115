import SU5SatinWakePhysicalGramNovember8

/-!
A PB.4 / LX.2 investment. Use the staffed, **mixed** review observable: current
contracted with a locally compared curvature component. Take limit in the *same*
History as GramPace. In particular, the PV-sector amplitudes used in the limiting
Mark data do not vary with period `i` or cutoff `k`. The spacing `r_s` mode here
is for **paying the two-point Wake**, not itself an infrared interaction witness.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
namespace LoomForce
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP
     Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
     InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Papal Lamour.Bridge Celeste Exterior SpinReceipt Yoke Jewel EmberWind Hiro Onyx
open Regis.Head Regis.Head.Brecht Regis.Circuit
open YM.Stationary (Gaia)

variable (P : Spine) {s i k n : ℕ}
local notation "Λ" => P.par
local notation "Γ" => P.run
open Vale (hat)

/-- Keep the *order* of limits, rung-outer. -/
abbrev successive : Filter (ℕ × ℕ) := atTop.curry atTop
abbrev takenVolume (P : Spine) : ℕ → ℕ := P.period ∘ P.projection.rows
abbrev takenCutoff (P : Spine) : ℕ → ℕ := P.cutoff ∘ P.projection.columns
abbrev matterSide (P : Spine) (s : ℕ) (n : ℕ) := side P.run (takenVolume P n) s
abbrev background (P : Spine) (c : ℕ × ℕ) := P.par.V.L.H (P.run.uv (takenCutoff P c.2) - c.1)
def gaugeAt (P : Spine) (W V : ℕ → Staff) (f : ℕ → ℕ) (c : ℕ × ℕ) : ℂ :=
  gaugeCoupon (W c.1) (V c.1) (matterSide P c.1 (f c.2)) (background P (c.1,f c.2))
def spinAt (P : Spine) (W V : ℕ → Staff) (f : ℕ → ℕ) (c : ℕ × ℕ) : ℂ :=
  spinCoupon P.run c.1 (takenVolume P (f c.2)) (takenCutoff P (f c.2)) (W c.1) (V c.1)

lemma matterSide_grows (s : ℕ) : Tendsto (matterSide P s) atTop atTop :=
  (count_la Γ s).comp (P.law.pick.grow_i.comp P.history.growsA).tendsto_atTop

omit P in
lemma translateGaugeTable (W V : Staff) (x : ℝ) (n : Side) (M : Precision.Bed) :
    (x : ℂ)^4 * gaugeCoupon W V n M = acePower SU.group
      (magnify M x (plaquette W.face.2) (plaquette V.face.2) (W.face.1 - V.face.1) (More n)) := by
  unfold gaugeCoupon acePower magnify
  let a := wrap (More n)
  let X := W.face.1
  let Y := V.face.1
  rw [rimflare (More n) M (a X) (a Y) (X - Y) (map_sub a X Y).symm,
    rimflare (More n) M (a (X - Y)) 0 (X - Y) (sub_zero _)]
  ring

variable {x y : Gaia} {A : ℝ} (hA : 0 < A) {W V : ℕ → Staff} {F D : PlaqAxes}
  {f : ℕ → ℕ} (u : StrictMono f)
local notation "scale_" P:max s:max => sPow (Spine.par P) s A

include hA u
lemma gauge_fee (hf : ∀ s, (W s).face.2 = F) (hg : ∀ s, (V s).face.2 = D)
    (p : Tendsto (fun i => riseX (scale_ P i) ((W i).face.1 - (V i).face.1)) atTop (𝓝 x))
    (g : x ≠ 0) :
    Tendsto (fun c : ℕ × ℕ => (scale_ P c.1 : ℂ)^4 * gaugeAt P W V f c)
      successive (𝓝 (speckleV F D SU.group x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  apply eventually_curry_iff.mpr
  have hpos (s : ℕ) : 0 < scale_ P s := BProof.coin_pos ..
  filter_upwards [manifold F D (Λ).K.top.clip (Λ).V.W.parcel (Λ).K.width
    (zero_lt_one.trans_le (Λ).V.up) hpos (sPower_pay Λ hA) (U := fun i => (W i).face.1)
    (W := fun i => (V i).face.1) p g (ε/2) (half_pos hε) SU.group] with s w
  filter_upwards [((matterSide_grows P s).comp u.tendsto_atTop).eventually w] with i v
  let G := background P (s, f i)
  let n := matterSide P s (f i)
  have hv := (Λ).V.L.roof (P.run.uv (takenCutoff P (f i)) - s)
  change dist (_ * gaugeCoupon (W s) (V s) n G) _ < _
  rw [translateGaugeTable, hf, hg]
  exact lt_of_le_of_lt (v G hv.1 (hv.2.1 _)) (half_lt_self hε)

omit hA u P in
lemma translateSpinTable (N : Side) (R : ℕ) (w v : Cover) (L G : Twah.DirSpin) (j : ℕ)
    (M : Jill.Male) : diced R w v L G N j M = (R : ℂ)^6 * diced 1 w v L G N j M := by
  have h (L G : Twah.DirSpin) (w v : Cover) :
      dietary R w v L G N j M = (R : ℂ)^3 * dietary 1 w v L G N j M := by
    unfold dietary
    simp_rw [in_transcript, Emu.hopF]
    push_cast
    ring
  unfold diced
  rw [h L G, h G L]; ring

local notation "ratio_" P:max s:max => frayR (Spine.par P) A s
local notation "sizer_" P:max s:max => zoomR (Spine.par P) A s

lemma spin_fee {L G : Twah.DirSpin} (hf : ∀ s, (W s).spin = L)
    (hg : ∀ s, (V s).spin = G)
    (p : Tendsto (fun i => riseX (sizer_ P i) ((W i).u - (V i).u)) atTop (𝓝 y))
    (g : y ≠ 0) :
    Tendsto (fun c : ℕ × ℕ => (sizer_ P c.1 : ℂ)^6 * spinAt P W V f c)
      successive (𝓝 (shotR L G (X:=y))) := by
  let U := fun i => (W i).u
  let T := fun i => (V i).u
  have hh (i : ℕ) : 0 < sizer_ P i := Nat.ceil_pos.mpr (half_pos (BProof.coin_pos ..))
  have hu := nontrivial_spin Λ
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  apply eventually_curry_iff.mpr
  filter_upwards [travel_feast (Λ).K.j L G hu (zoomR Λ A) (zoom_grows Λ hA) hh T U p g
    (ε/2) (half_pos hε)] with s w
  filter_upwards [((matterSide_grows P s).comp u.tendsto_atTop).eventually w] with i v
  change dist ((sizer_ P s : ℂ)^6 * diced 1 _ _ (W s).spin (V s).spin (matterSide P s (f i)) _ _) _ < _
  rw [hf s, hg s]
  rw [← translateSpinTable]
  apply lt_of_le_of_lt (v ?_ _) (half_lt_self hε)
  exact Vale.val_e ..

omit P hA u in
lemma fstSucc : Tendsto Prod.fst successive atTop := tendsto_fst.mono_left curry_le_prod

omit u hA in
lemma reachesSucc (β : ℕ → ℝ)
    (w : Pooling Γ (takenVolume P) (takenCutoff P) f β) :
    Tendsto (fun c : ℕ × ℕ => (reachCost Γ c.1 (takenVolume P (f c.2))
      (takenCutoff P (f c.2)) (κFix β c.1) : ℂ)) successive (𝓝 1) := by
  refine Tendsto.curry (f := fun i n => (reachCost Γ i (takenVolume P (f n))
    (takenCutoff P (f n)) (κFix β i) : ℂ)) (Eventually.of_forall (fun s : ℕ => ?_))
  have h := @Complex.continuous_ofReal
  simpa only [Function.comp_def, Complex.ofReal_one] using h.continuousAt.tendsto.comp (Gathering Γ w s)

def ampl (P : Spine) (s : ℕ) (I : ℝ) : ℂ := (sPow P.par s I : ℂ)^5 / 16
omit u hA in
lemma split_ampl (s : ℕ) :
    ampl P s A = ((ratio_ P s : ℂ)^3/2)*(sizer_ P s:ℂ)^3*(scale_ P s:ℂ)^2 := by
  have hy (i : ℕ) : 0 < sizer_ P i := Nat.ceil_pos.mpr (half_pos (BProof.coin_pos ..))
  let u : ℝ := ratio_ P s
  let y : ℕ := sizer_ P s
  let z : ℝ := scale_ P s
  have h : 2*(y:ℝ)*u = z := by
    change 2*(y:ℝ)*(z/(2*(y:ℝ)))=z
    have hz : 0 < 2*(y:ℝ) := mul_pos two_pos (Nat.cast_pos.mpr (hy s))
    exact mul_div_cancel₀ z hz.ne'
  have he : (z:ℂ) = 2*(y:ℂ)*(u:ℂ) := by exact_mod_cast h.symm
  change (z:ℂ)^5 /16=(u^3 / 2 : ℂ)*(y:ℂ)^3*(z:ℂ)^2
  rw [he]; ring

variable {β : ℕ → ℝ} {L G : Twah.DirSpin}

lemma wale_limit (w : Pooling Γ (takenVolume P) (takenCutoff P) f β)
    (hf : ∀ s, (W s).face.2 = F) (hg : ∀ s, (V s).face.2 = D)
    (p : Tendsto (fun i => riseX (scale_ P i) ((W i).face.1 - (V i).face.1)) atTop (𝓝 x))
    (g : x ≠ 0)
    (hx : ∀ s, (W s).spin = L) (hy : ∀ s, (V s).spin = G)
    (q : Tendsto (fun i => riseX (sizer_ P i) ((W i).u - (V i).u)) atTop (𝓝 y))
    (v : y ≠ 0) :
    Tendsto (fun c : ℕ × ℕ => (ampl P c.1 A)^2 * wale Γ c.1
        (takenVolume P (f c.2)) (takenCutoff P (f c.2)) (W c.1) (V c.1) (κFix β c.1))
      successive (𝓝 (((1/2:ℂ)^2 * shotR L G (X:=y)) * speckleV F D SU.group x)) := by
  have hh : Tendsto (fun c : ℕ × ℕ => (ratio_ P c.1 : ℂ)) successive (𝓝 (1:ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_one] using (Complex.continuous_ofReal.continuousAt.tendsto.comp
      ((fray_lift Λ hA).comp fstSucc))
  have he := (((((hh.pow 3).div_const 2).pow 2).mul (spin_fee P hA u hx hy q v)).mul
    (gauge_fee P hA u hf hg p g)).mul ((reachesSucc P β w).pow 2)
  rw [one_pow,one_pow,mul_one] at he
  refine he.congr ?_
  intro c
  rw [split_ampl P]
  unfold spinAt gaugeAt wale background matterSide; ring


open Pressure BProof Worth Worth.Pays WakeInvestment
local notation "χ" P:max s:max => WakeInvestment.chip (hat (Spine.par P).R.L (Spine.par P).x s) (-3)
omit hA u in
lemma ampl_chip (A : ℝ) (d : ℕ) : Tendsto (fun s => ‖ampl P s A‖^d * χ P s)
    atTop (𝓝 0) := by
  have he := Pays.pot (Pays.right ((16 : ℝ)⁻¹) (Pays.pot (whole 0 A 0) 5)) d
  have hf := Pays.limit (Pays.times he (whole (-3/400000) 0 0)) (Or.inl (by norm_num))
  refine (hf.comp (turnover Λ)).congr ?_
  intro s
  simp only [comp_apply]
  rw [ampl,norm_div,norm_pow,Complex.norm_real, Real.norm_of_nonneg (BProof.coin_pos ..|>.le)]
  change (_ * _) ^ d * χ P s = (((_ : ℝ)^5/‖((16:ℕ):ℂ)‖)^d)*_
  rw [Complex.norm_natCast,div_eq_mul_inv]; norm_num

section elected
local notation "Π" => P.calibration

/-- stencils include the chapter's rung amplitude. -/
def weaving (P : Spine) (A : ℝ) (W : Staff) (r s : ℕ) (β : ℕ → ℝ) : Papal.Weaver :=
  ampl P s A • W.rungWeave (κFix β s) r (temp (hat P.par.R.L P.par.x s))
omit u hA in
lemma weaving_ok (W : Staff) (A : ℝ) (r w s : ℕ) (β : ℕ → ℝ) (p : W.Pays r w) :
    InTest Π true (W.skyRent r) false (Papal.household Π (weaving P A W r s β)) :=
  (W.letterBudget (κFix β s) Π _ p).smul _ -- try

/-- bare consultation (at observing rung s). -/
abbrev finiteE (P : Spine) (s n : ℕ) (F : Papal.Weaver) : ℂ :=
  Journey.compass P.run (takenVolume P n) (takenCutoff P n) s (F (matterSide P s n))
abbrev infiniteE (P : Spine) (s : ℕ) (F : Papal.Weaver) : ℂ :=
  P.E s (Papal.household P.calibration F)
omit u hA in
lemma reading (s : ℕ) (F : Papal.Weaver) (p : TestFamily Π true (Papal.household Π F)) :
    Tendsto (fun n => finiteE P s n F) atTop (𝓝 (infiniteE P s F)) := by
  refine (sharp_on_track Γ P.law P.history s p).congr ?_
  intro n
  change Journey.compass Γ _ _ s (expSrc _ s (takenVolume P n) P.large _) = _
  rw [lift_book]

omit hA u in
lemma finiteE_scale (s n : ℕ) (a : ℂ) (F : Papal.Weaver) :
    finiteE P s n (a • F) = a * finiteE P s n F := by
  unfold finiteE
  rw [Pi.smul_apply]
  unfold Journey.compass
  rw [mark_smul, mul_div_assoc]

structure PaidPair (P : Spine) (I : ℝ) (W V : ℕ → Staff) (r : ℕ → ℕ) : Prop where
  positive : 0 < I
  rents : ∀ᶠ s : ℕ in atTop, ∀ᶠ n : ℕ in atTop,
    ∃ (e w : ℕ) (o : Seat (matterSide P s n)),
      (e : ℝ) ≤ sPow P.par s I ∧ (w : ℝ) ≤ sPow P.par s I ∧
        (W s).Pays (r s) w ∧ (V s).Pays (r s) w ∧
        (W s).tenancy (matterSide P s n) (r s) Staff.clearance e o ∧
        (V s).tenancy (matterSide P s n) (r s) Staff.clearance e o

variable {r : ℕ → ℕ} {I : ℝ} (grams : P.PhysicalWakeGram)

local notation "full_" W:max r:max s:max => weaving P A (W s) (r s) s β
omit u hA

private lemma finite_mul (W V : Staff) (a b : ℕ) (A : ℝ) (n : ℕ) :
    finiteE P a n (weaving P A W b a β * weaving P A V b a β) =
    (ampl P a A)^2 * finiteE P a n (W.rungWeave (κFix β a) b (temp (hat (Λ).R.L (Λ).x a)) *
      V.rungWeave (κFix β a) b (temp (hat (Λ).R.L (Λ).x a))) := by
  unfold weaving
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, ← pow_two, finiteE_scale]

include grams
lemma three_bills (w : Pooling Γ (takenVolume P) (takenCutoff P) f β)
    (paid : PaidPair P I W V r) :
    ∀ᶠ c : ℕ × ℕ in successive,
      ‖finiteE P c.1 (f c.2) (full_ W r c.1)‖ ≤ ‖ampl P c.1 A‖ * χ P c.1 ∧
      ‖finiteE P c.1 (f c.2) (full_ V r c.1)‖ ≤ ‖ampl P c.1 A‖ * χ P c.1 ∧
      ‖finiteE P c.1 (f c.2) (full_ W r c.1 * full_ V r c.1) - (ampl P c.1 A)^2 *
          wale Γ c.1 (takenVolume P (f c.2)) (takenCutoff P (f c.2)) (W c.1) (V c.1) (κFix β c.1)‖
        ≤ ‖ampl P c.1 A‖ ^ 2 * χ P c.1 := by
  apply eventually_curry_iff.mpr
  filter_upwards [grams I paid.positive, paid.rents] with s h v
  filter_upwards [w.up.tendsto_atTop.eventually h,w.up.tendsto_atTop.eventually v] with n p q
  obtain ⟨e,y,o,t,g,H,J,c,d⟩ := q
  let B := ampl P s A
  have U := paidFix Γ w P.large s
  refine ⟨?_,?_,?_⟩
  · unfold weaving
    rw [finiteE_scale,norm_mul]; exact mul_le_mul_of_nonneg_left (p.single H c U t g) (norm_nonneg B)
  · unfold weaving
    rw [finiteE_scale,norm_mul]; exact mul_le_mul_of_nonneg_left (p.single J d U t g) (norm_nonneg B)
  rw [finite_mul, ←mul_sub,norm_mul,norm_pow]
  exact mul_le_mul_of_nonneg_left (p.duo H c J d U t g) (sq_nonneg ‖B‖)

abbrev wakeFee (F D : PlaqAxes) (L G : Twah.DirSpin) (x y : Gaia) : ℂ :=
  ((1/2:ℂ)^2 * shotR L G (X:=y)) * speckleV F D SU.group x

omit grams in
lemma tendByAmpl (d : ℕ) {z : ℕ × ℕ → ℂ}
    (t : ∀ᶠ c : ℕ × ℕ in successive, ‖z c‖ ≤ ‖ampl P c.1 A‖^d * χ P c.1) :
    Tendsto z successive (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall (fun i => norm_nonneg (z i))) t
    ((ampl_chip P A d).comp fstSucc)

include hA
lemma finite_ledger (w : Pooling Γ (takenVolume P) (takenCutoff P) f β)
    (paid : PaidPair P I W V r)
    (hf : ∀ s, (W s).face.2 = F) (hg : ∀ s, (V s).face.2 = D)
    (p : Tendsto (fun i => riseX (scale_ P i) ((W i).face.1 - (V i).face.1)) atTop (𝓝 x))
    (g : x ≠ 0)
    (hx : ∀ s, (W s).spin = L) (hy : ∀ s, (V s).spin = G)
    (q : Tendsto (fun i => riseX (sizer_ P i) ((W i).u - (V i).u)) atTop (𝓝 y))
    (v : y ≠ 0) :
    Tendsto (fun c : ℕ × ℕ => finiteE P c.1 (f c.2) (full_ W r c.1)) successive (𝓝 0) ∧
    Tendsto (fun c : ℕ × ℕ => finiteE P c.1 (f c.2) (full_ V r c.1)) successive (𝓝 0) ∧
    Tendsto (fun c : ℕ × ℕ => finiteE P c.1 (f c.2) (full_ W r c.1 * full_ V r c.1))
      successive (𝓝 (wakeFee F D L G x y)) := by
  have he := three_bills (A:=A) P grams w paid
  let d (c : ℕ × ℕ) := (ampl P c.1 A)^2 * wale Γ c.1 (takenVolume P (f c.2))
    (takenCutoff P (f c.2)) (W c.1) (V c.1) (κFix β c.1)
  let Z (c : ℕ × ℕ) := finiteE P c.1 (f c.2) (full_ W r c.1 * full_ V r c.1)
  have ht : Tendsto (fun c => Z c - d c) successive (𝓝 0) := tendByAmpl (A:=A) P 2 (he.mono (fun i h => h.2.2))
  have hv := ht.add (wale_limit P hA w.up w hf hg p g hx hy q v)
  rw [zero_add] at hv
  refine ⟨tendByAmpl (A:=A) P 1 ?_, tendByAmpl (A:=A) P 1 ?_, hv.congr ?_⟩
  · filter_upwards [he] with i h; simpa only [pow_one] using h.1
  · filter_upwards [he] with i h; simpa only [pow_one] using h.2.1
  intro c; exact sub_add_cancel (Z c) (d c)

omit P grams hA in
lemma bySuccessive {a : ℕ × ℕ → ℂ} {f : ℕ → ℂ} {z : ℂ}
    (w : ∀ᶠ s : ℕ in atTop, Tendsto (fun i => a (s,i)) atTop (𝓝 (f s)))
    (q : Tendsto a successive (𝓝 z)) : Tendsto f atTop (𝓝 z) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [w,eventually_curry_iff.mp (Metric.tendsto_nhds.mp q (ε/2) (half_pos hε))]
    with s p h
  exact lt_of_le_of_lt (le_of_tendsto (p.dist (tendsto_const_nhds (x := z))) (h.mono fun i v => v.le)) (half_lt_self hε)

/-- A two-point payment on the P.E prescription of the very elected Course. -/
lemma booked_ledger (w : Pooling Γ (takenVolume P) (takenCutoff P) f β)
    (paid : PaidPair P I W V r)
    (hf : ∀ s, (W s).face.2 = F) (hg : ∀ s, (V s).face.2 = D)
    (p : Tendsto (fun i => riseX (scale_ P i) ((W i).face.1 - (V i).face.1)) atTop (𝓝 x))
    (g : x ≠ 0)
    (hx : ∀ s, (W s).spin = L) (hy : ∀ s, (V s).spin = G)
    (q : Tendsto (fun i => riseX (sizer_ P i) ((W i).u - (V i).u)) atTop (𝓝 y))
    (v : y ≠ 0) :
    Tendsto (fun s => infiniteE P s (full_ W r s)) atTop (𝓝 0) ∧
    Tendsto (fun s => infiniteE P s (full_ V r s)) atTop (𝓝 0) ∧
    Tendsto (fun s => infiniteE P s (full_ W r s * full_ V r s) -
      infiniteE P s (full_ W r s) * infiniteE P s (full_ V r s)) atTop
      (𝓝 (wakeFee F D L G x y)) := by
  let a s := full_ W r s
  let b s := full_ V r s
  have he : ∀ᶠ s in atTop, TestFamily Π true (household Π (a s)) ∧
      TestFamily Π true (household Π (b s)) := by
    filter_upwards [paid.rents] with s H
    obtain ⟨n,e,w,o,_,_,x,y,h⟩ := H.exists
    exact ⟨aux_test (weaving_ok P _ _ _ _ _ _ x),aux_test (weaving_ok P _ _ _ _ _ _ y)⟩
  obtain ⟨U,S,H⟩ := finite_ledger P hA grams w paid hf hg p g hx hy q v
  have Hu:= bySuccessive (f:=fun s=>infiniteE P s (a s))
    (he.mono fun s h => (reading P s _ h.1).comp w.up.tendsto_atTop) U
  have Hv:= bySuccessive (f:=fun s=>infiniteE P s (b s))
    (he.mono fun s h => (reading P s _ h.2).comp w.up.tendsto_atTop) S
  have Hw:= bySuccessive (f:=fun s=>infiniteE P s (a s * b s))
    (he.mono fun s h => (reading P s (a s * b s) (h.1.mul h.2)).comp w.up.tendsto_atTop) H
  have hq := Hw.sub (Hu.mul Hv)
  rw [zero_mul,sub_zero] at hq
  exact ⟨Hu,Hv,hq⟩

#print axioms booked_ledger
end elected
end LoomForce
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

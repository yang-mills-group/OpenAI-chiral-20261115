import YM.SU5.LoomForce.GaugeWake

/-!
# Mixed-Wake readers: P.E version. Uniform in particular already buying *higher*
geometry powers on the given appointments, any insertions and any arity (before
pricing), side order with physical seating. Keep even occupied-sector Wake in
this certificate, for later re-use with Torque and IA.1 ledgers.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
open Function Filter Metric Fock Finset Lat Lattice Laurent Next.Free Cube Tulip Scroll Spire Pastry RP Branch
  Wilson Phase SU Rush Mir Reflect Lifted Window Skye Dial Analysis MeasureTheory
open Lamour Lamour.Bridge Celeste Clock Hookah Hiro RG Girt
open Py Py.Rate Py.Rate.LocalLimit Preparation Yoke Papal Tapestry Journey
open Ballad EmberWind CF.Pannier.Chancel WakeInvestment Gleam Gleam.Wake
open Jewel Onyx Vale Pressure
open YM.Stationary (Gaia)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology ContDiff Classical
universe u
variable {I : Type u} [Fintype I] (P : Spine) (K : P.Register) {X : ℝ}{Mc:ℕ} (J: PreparedInvestment P K X Mc)
local notation "Γ" => P.run
local notation "Λ" => P.par

-- Staff stamp using actual CP1 amplitudes. Mixed Force at /16 from
-- raw 1-spin vertex. Tone (incl all six clans) literally from same Appoint q_Z
-- (our real proof below elects even these with the mixed apertures).
def stitch (P : Spine) (A : ℝ) (s : ℕ) (β : ℕ →ℝ) (W : Staff) (b : ℕ) (T : Sewer) : Papal.Weaver :=
   ((frayR P.par A s:ℂ)^3/2) • spool (zoomR P.par A s) (glow P.par A s)
    W b (κFix β s) (temp (hat P.par.R.L P.par.x s)) T
def threadRoll (tag : I→ Sewer) (L : List I) (A : ℝ) (s : ℕ) (β : ℕ →ℝ)
    (W : I→ Staff)(b:ℕ) : Papal.Weaver := (L.map fun i=> stitch P A s β (W i) b (tag i)).prod
variable {A H:ℝ} {f :ℕ→ℕ} (W:ℕ→I→Staff) {b : ℕ→ℕ} {β:ℕ→ℝ}
variable (z:Pooling P.run (takenVolume P) (takenCutoff P) f β)

structure Packs (P : Spine) (T : ℝ) (W : ℕ → I → Staff) (r : ℕ → ℕ) : Prop where
  positive : 0<T
  walls : ∀ᶠ s : ℕ in atTop, ∀ᶠ n : ℕ in atTop, ∃ (e w:ℕ) (o:Seat (matterSide P s n)),
      (e:ℝ) ≤ sPow P.par s T ∧ (w:ℝ) ≤ sPow P.par s T ∧ ∀ i,
        (W s i).tenancy (matterSide P s n) (r s) Staff.clearance e o ∧
        (W s i).Pays (r s) w

-- include order to bill labels even if different manifestations of one species;
-- do require the distinct letters which incur all different-position costs here.
structure Consigned (P : Spine) (A : ℝ) (V : ℕ → I → Staff) (tag : I → Twah.DirSpin) (U : I → PlaqAxes) (x y:I → Gaia) : Prop where
  positive : 0<A
  spin (i:I) : Appoint P.par A (fun s=> (V s i).u) (x i)
  shelf (i : I) : Tendsto (fun n=> riseX (sPow P.par n A) (V n i).face.1) atTop (𝓝 (y i))
  cost (s:ℕ)(i:I) : (V s i).face.2= U i
  color(s:ℕ)(i:I) : (V s i).spin = tag i
  ties(i j:I) : x i=x j →∀ᶠ s:ℕ in atTop,(V s i).u=(V s j).u

local notation "β₀" s:max=> κFix β s
local notation "𝕖" P:max A:max L:max W:max s:max b:max t:max ρ:max => ream t L (zoomR (Spine.par P) A s) (glow (Spine.par P) A s) W b ρ (temp (hat (P).par.R.L (P).par.x s))
local notation "F_" P:max z:max => matterSide P z
local notation "I_" P:max v:max => takenVolume P v
local notation "κ_" P:max v:max => takenCutoff P v
variable {G:I→ Twah.DirSpin}{F:I→PlaqAxes}{x y:I→ Gaia}(u:Packs P H W b)
    (v:Consigned P A W G F x y) (tag:I→ Sewer) (L:List I) (p:L.Pairwise (fun i j=> y i≠ y j))
local notation "Z" => wakeZ G x
local notation "Y" => wakeG y F
local notation "Z_" s:max n:max=> readsZ P A (W s) s n
local notation "Y_" s:max n:max=> offerG P A s n β (W s)
local notation "P_" s:max=> 𝕖 P A L (W s) s (b s) tag (β₀ s)
include J u v z

lemma signal_bound : ∀ᶠ c : ℕ × ℕ in successive,
    ‖finiteE P c.1 (f c.2) (P_ c.1) - quoted tag L (Z_ c.1 (f c.2)) (Y_ c.1 (f c.2))‖ ≤
      WakeInvestment.chip (hat (Λ).R.L (Λ).x c.1) (-3):=by
  let m:= L.length; let M:= (booths tag L).toFinset
  have h(i j): Tendsto (fun c : ℕ × ℕ=> (Z_ c.1 (f c.2)) i j) successive (𝓝 (Z i j)):= reachingZ (W:=W) P v.positive v.spin v.ties (fun i s=>v.color s i) z.up i j
  have h1 (r : Route I) : Tendsto (fun c : ℕ × ℕ => ‖quoteSpin r (Z_ c.1 (f c.2))‖) successive
      (𝓝 ‖quoteSpin r Z‖):=(attend_spin h r).norm
  -- Fund all coefficient requests in one go at this arity
  obtain ⟨C,h0,hu⟩:= (((eventually_gt_atTop (0:ℝ))).and ((eventually_all_finset M).mpr
    (fun r _=>eventually_gt_atTop ‖quoteSpin r Z‖))).exists
  let K' := Fintype.card (loomG I)
  have hw:= eventually_curry_iff.mp ((eventually_all_finset M).mpr
    (fun r hr=> (h1 r).eventually (ge_mem_nhds (hu r hr))))
  obtain ⟨T,hT,hp⟩:= office_opens Λ m (booths tag L).length K' C H A h0.le u.positive v.positive
  obtain ⟨i,hi⟩:=J.investment
  let α:ℝ := 1/2; have hα:0<α:=by unfold α; norm_num; -- tune
  have U:α<1:=by unfold α; norm_num
  apply eventually_curry_iff.mpr
  filter_upwards [hp,u.walls,hw, Yoke.sails.{u} Γ P.law P.history hi J.dispatch J.rocky.merit (2*L.length) m hT hα U.le] with s hs hX H' v'
  filter_upwards [z.up.tendsto_atTop.eventually (P.history.finance s), z.up.tendsto_atTop.eventually v',
    z.up.tendsto_atTop.eventually hX, H'] with n v0 v1 v2 c
  let a:=f n; let i:=takenVolume P a; let k:=takenCutoff P a; let V:=W s; let S':=scout V (side Γ i s); let r:=b s
  obtain ⟨e,w,o,hL,hW,p⟩:=v2; let Q:=Z_ s a; let φ:=lensPay Q tag L (glow Λ A s)
  have p' := Broom_tactic (H:=P.large) Γ s i k V tag L h0.le hs hL hW (paidFix Γ z P.large s) (fun i=> (p i).2) (fun i=>(p i).1) Q (fun i p=>c i (List.mem_toFinset.mpr p)) U v0.enters v1.2.1 rfl
  have he := v1.2.2 (2*e) (actual_rents Γ s i tag L A V (b s) e (β₀ s) o) (β₀ s) S' φ p'
  change ‖_ - quoted tag L Q (hueCost _ _ _ _ _ _ _)‖ ≤ _; rw [←hueCost_collect]; exact he

include p
lemma full_limit : Tendsto (fun c : ℕ × ℕ => finiteE P c.1 (f c.2) (P_ c.1)) successive
     (𝓝 (quoted tag L Z Y)):= by
  let d(c:ℕ×ℕ) := quoted tag L (Z_ c.1 (f c.2)) (Y_ c.1 (f c.2)); let payF (c : ℕ × ℕ):= finiteE P c.1 (f c.2) (P_ c.1)
  have hx : L.Pairwise (fun i j=> ∀ a b,Tendsto (fun c : ℕ × ℕ => (Y_ c.1 (f c.2)) (i,a) (j,b)) successive (𝓝 (wakeG y F (i,a) (j,b)))) := by
    apply p.imp; intro i j t a b
    exact reachingG (F:=F) (y:=y) (W:=W) P z v.positive (i,a) (j,b) v.shelf v.cost t
  have hp: Tendsto d successive (𝓝 (quoted tag L Z Y)) := attend_quoted (tag:=tag) (W:=Y) (P:=successive) («Z»:=wakeZ G x) (ZT:=fun c : ℕ × ℕ => Z_ c.1 (f c.2))
    (WT:=fun c : ℕ × ℕ => Y_ c.1 (f c.2)) (reachingZ (W:=W) P v.positive v.spin v.ties (fun i s=>v.color s i) z.up)
    L hx
  have hx: Tendsto (fun c=> payF c-d c) successive (𝓝 0):= by
    refine tendByAmpl (A:=A) P 0 ?_
    simpa only [pow_zero,one_mul] using signal_bound P K J W z u v tag L -- tune
  have he:= hx.add hp; rw [zero_add] at he; exact he.congr fun c=>sub_add_cancel (payF c) (d c)

-- restore as physical stamps (the CP1 convention)
omit J u v z p
omit [Fintype I] in
lemma restore (v:ℕ) : threadRoll P tag L A v β (W v) (b v)=
    ((frayR Λ A v : ℂ)^3/2)^L.length • (P_ v):= by
  let c:=(frayR Λ A v : ℂ)^3/2
  induction L with
  | nil=> simp [threadRoll,ream]
  | cons i L ih=>
    let M:=spool (zoomR Λ A v) (glow Λ A v) (W v i) (b v) (κFix β v) (temp (hat P.par.R.L P.par.x v)) (tag i)
    let N:=𝕖 P A L (W v) v (b v) tag (β₀ v)
    rw [List.length_cons,pow_succ']; change ((c • M)*threadRoll P tag L A v β (W v) (b v))=(c * c^L.length) • (M*N)
    rw [ih,Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]

include J u v z p
lemma span_bill : Tendsto (fun c : ℕ × ℕ => finiteE P c.1 (f c.2) (threadRoll P tag L A c.1 β (W c.1) (b c.1))) successive
     (𝓝 ((1/2:ℂ)^L.length*quoted tag L Z Y)) := by
  have hh : Tendsto (fun c : ℕ × ℕ => (frayR Λ A c.1 : ℂ)) successive (𝓝 (1:ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_one] using (Complex.continuous_ofReal.continuousAt.tendsto.comp
      ((fray_lift Λ v.positive).comp fstSucc))
  have he := ((((hh.pow 3).div_const 2).pow L.length).mul (full_limit P K J W z u v tag L p))
  rw [one_pow] at he; refine he.congr fun i'=>?_ ; rw [restore,finiteE_scale]

/-- any-fixed mixed Wake in the elected P family, unselected valuation. -/
lemma true_books : Tendsto (fun s=> infiniteE P s (threadRoll P tag L A s β (W s) (b s))) atTop
    (𝓝 ((1/2:ℂ)^L.length*quoted tag L Z Y)) := by
  apply bySuccessive _ (span_bill P K J W z u v tag L p)
  filter_upwards [u.walls] with s t; obtain ⟨n,e,w,o,_,_,Q'⟩:= t.exists
  have h:TestFamily P.calibration true (household P.calibration (threadRoll P tag L A s β (W s) (b s))) := by
    rw [restore]; apply aux_test (_: InTest _ true (wholeSky (W s) (b s) L) false _)
    exact (ream_label _ _ _ tag (W s) (fun i=> (Q' i).2) _ L P.calibration).smul _
  exact (reading P s (threadRoll P tag L A s β (W s) (b s)) h).comp z.up.tendsto_atTop

#print axioms signal_bound
#print axioms span_bill
#print axioms true_books
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette

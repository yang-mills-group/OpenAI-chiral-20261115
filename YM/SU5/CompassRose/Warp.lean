import SU5SatinWakePhysicalGramNovember8

/-!
At the physical ground extension, two distinct filters are important: rung (`s`),
and refinement of period & cutoff with `s` held FIXED. Tests in this file are paid
on those exact data, not price comparisons on an alternative unelected Gaussian process.

Use microscope coordinates of WakeInvestment (will freeze an `s` after successful estimate;
limits in `s` here are not themselves fixed-scale nonvanishing).
-/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 500000
set_option quotPrecheck false
set_option linter.unusedSectionVars false

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine Preparation.Yoke
open CF.Velvet CF.Pannier.Chancel CF.Pannier.Chancel.Rous Pressure
open YM.Stationary (Gaia)
open Onyx Regis.Circuit Regis.Head Regis.Head.Brecht Exterior Hiro

namespace Rose
open EmberWind Jewel

/-- Nested limit; `s` then `n` in binder order, i.e., take volume/cutoff first. -/
abbrev bobbin : Filter (ℕ × ℕ) := Filter.bind atTop fun s => Filter.map (Prod.mk s) atTop

lemma bobbin_for {p : ℕ × ℕ → Prop} :
    (∀ᶠ sn in bobbin, p sn) ↔ ∀ᶠ s in atTop, ∀ᶠ n in atTop, p (s,n) := by
  rw [bobbin, eventually_bind]; simp_rw [eventually_map]

instance : bobbin.NeBot := neBot_iff.mpr (by
  intro h
  obtain ⟨s,g⟩ := (bobbin_for.mp (eventually_false_iff_eq_bot.mpr h)).exists
  obtain ⟨t,u⟩ := g.exists
  contradiction)
lemma runway : Tendsto Prod.fst bobbin atTop := fun S h =>
  bobbin_for.mpr ((show ∀ᶠ s : ℕ in atTop, s ∈ S from h).mono fun _ p => Eventually.of_forall fun _ => p)

/-- reuse of the inner path: take the thinning limit at each fixed rung at accuracy which
may depend even on that rung and test. No claim of uniform modulus in this thinning. -/
lemma furl {X : Type*} [TopologicalSpace X] {f : ℕ × ℕ → X} {g : ℕ → X} {x : X}
    (p : ∀ᶠ s in atTop, Tendsto (fun n => f (s,n)) atTop (𝓝 (g s)))
    (q : Tendsto g atTop (𝓝 x)) : Tendsto f bobbin (𝓝 x) := by
  intro A hA
  obtain ⟨u,v,t,a⟩ := mem_nhds_iff.mp hA
  apply bobbin_for.mpr
  filter_upwards [p,q (t.mem_nhds a)] with s p hs
  exact (p.eventually (t.mem_nhds hs)).mono fun n h => v h

/-- Conversely estimates at all sufficiently late volumes with permits even for varying tests
pass through the inner limit for each outer-rung data item. -/
lemma reels {X : Type*} [PseudoMetricSpace X] {f : ℕ × ℕ → X} {g : ℕ → X} {x : X}
    (p : ∀ᶠ s in atTop, Tendsto (fun n => f (s,n)) atTop (𝓝 (g s)))
    (q : Tendsto f bobbin (𝓝 x)) : Tendsto g atTop (𝓝 x) := by
  refine Metric.tendsto_nhds.mpr fun d a => ?_
  filter_upwards [p,bobbin_for.mp (Metric.tendsto_nhds.mp q (d / 2) (half_pos a))] with s p q
  exact lt_of_le_of_lt (le_of_tendsto (p.dist tendsto_const_nhds) (q.mono fun _ h => h.le)) (half_lt_self a)

variable (P : Spine)
/-- NOT period/cutoff values resp., the actual indexes in the coherent history. -/
abbrev period (u : ℕ) := P.period (P.projection.rows u)
abbrev cutoff (u : ℕ) := P.cutoff (P.projection.columns u)
abbrev loom (s u : ℕ) := side P.run (period P u) s
abbrev orbitSize (f : ℕ → ℕ) (z : ℕ × ℕ) := loom P z.1 (f z.2)
abbrev Pools (v : ℕ → ℕ) (β : ℕ → ℝ) := Jewel.Pooling P.run (period P) (cutoff P) v β

lemma warp_pool (v : ℕ → ℕ) (hv : StrictMono v) :
    ∃ w β, StrictMono w ∧ Pools P (v ∘ w) β := Pooling.fettle P.run P.history hv

lemma thicken {f : ℕ → ℕ} (p : StrictMono f) (s : ℕ) :
    Tendsto (fun n => orbitSize P f (s,n)) atTop atTop :=
  (Papal.count_la P.run s).comp ((P.law.pick.grow_i.comp (P.history.growsA.comp p)).tendsto_atTop)

variable {f : ℕ → ℕ} {β : ℕ → ℝ} (p : Pools P f β) (q : PhysicalWakeGram P)
include p
lemma finance : ∀ s, ∀ᶠ n in atTop, Ferry P.run s (period P (f n)) (cutoff P (f n)) := fun s =>
  p.up.tendsto_atTop.eventually (P.history.finance s)
lemma range_paid (s : ℕ) : |κFix β s| ≤ 2 * bornQ P.par s := paidFix _ p P.large s
lemma reach_normalized : Tendsto
    (fun z : ℕ × ℕ => reachCost P.run z.1 (period P (f z.2)) (cutoff P (f z.2)) (κFix β z.1)) bobbin (𝓝 1) :=
  furl (g := fun _ => 1) (Eventually.of_forall fun s => Jewel.Gathering P.run p s) tendsto_const_nhds
include q in
lemma paces {I : ℝ} (h : 0 < I) : ∀ᶠ z in bobbin, GramPace P.run z.1 (period P (f z.2)) (cutoff P (f z.2)) I :=
  bobbin_for.mpr ((q I h).mono fun _ h => p.up.tendsto_atTop.eventually h)
omit p
local notation "R" => sPow P.par
local notation "χ" s:max => WakeInvestment.chip (hat P.par.R.L P.par.x s) (-3)
variable {A I : ℝ}

lemma rungs_pos (s : ℕ) : 0 < R s A := BProof.coin_pos ..

lemma budget_secondary (h : A < I) (C : ℝ) : ∀ᶠ s : ℕ in atTop, C * R s A < R s I := by
  filter_upwards [(turnover P.par).eventually (BProof.coin_budget (b:=A) (e:=I) (c:=0)
      (a:=0) (d:=0) (f:=0) (Or.inr (Or.inl ⟨rfl,h⟩)) C 1 zero_lt_one)] with s hs
  simpa only [one_mul] using hs

lemma rchip (m : ℕ) : Tendsto (fun s => (R s A)^m * χ s) atTop (𝓝 0) := by
  refine Metric.tendsto_nhds.mpr fun d a => ?_
  filter_upwards [(turnover P.par).eventually (BProof.coin_budget
    (a := (-3:ℝ)/400000) (d:=0) (c:=0) (b:=A*m) (e:=0) (f:=0) (Or.inl (by norm_num)) 1 d a)] with s t
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (mul_nonneg (pow_nonneg (rungs_pos P s).le m) (WakeInvestment.chip_pos ..).le)]
  simp only [sPow,WakeInvestment.chip,BProof.coin_pow,BProof.coin_mul,zero_mul,add_zero,zero_add]
  simpa only [one_mul,BProof.coin_zero,mul_one] using t

local notation "Z₀" s:max => zoomR P.par A s
lemma zoom_pos (s : ℕ) : 0 < Z₀ s := Nat.ceil_pos.mpr (half_pos (rungs_pos P s))
lemma scaled_due (i j : ℕ) (h : 0 < A) : Tendsto (fun s => (R s A)^i * (Z₀ s:ℝ)^j * χ s) atTop (𝓝 0) := by
  apply squeeze_zero' (g := fun s => (R s A)^(i+j)*χ s) ?_ ?_ (rchip P (i+j))
  · exact Eventually.of_forall fun _ => mul_nonneg (mul_nonneg (pow_nonneg (rungs_pos P ..).le _) (by positivity)) (WakeInvestment.chip_pos ..).le
  filter_upwards [(sPower_pay P.par h).eventually_ge_atTop 2] with s hs
  have hz : (Z₀ s:ℝ) ≤ R s A := by
    have hx : (Z₀ s:ℝ) < R s A/2+1 := Nat.ceil_lt_add_one (half_pos (rungs_pos P s)).le
    linarith only [hs,hx]
  have hp := rungs_pos (A:=A) P s
  have he := WakeInvestment.chip_pos (hat P.par.R.L P.par.x s) (-3)
  rw [pow_add]; gcongr

section bought
include p
variable {x y : Gaia} {u w : ℕ → Cover} (U : Appoint P.par A u x) (V : Appoint P.par A w y)

abbrev pupil (P : Spine) (s n : ℕ) := RootBook P.run (period P n) (cutoff P n) s

omit p in
lemma rise_step (r : ℝ) (x y : Cover) : riseX r (x - y) = riseX r x - riseX r y := by
  ext i
  change (↑((x-y) i):ℝ)/_ = _
  simp [riseX,moor]; ring

variable (L D : DirSpin) (F G : PlaqAxes)
include U V

lemma pair_spin (h : 0 < A) (e : x ≠ y) : Tendsto
    (fun sn : ℕ × ℕ => diced (Z₀ sn.1) (u sn.1) (w sn.1) L D (orbitSize P f sn)
      P.par.K.j (pupil P sn.1 (f sn.2)).J.M)
    bobbin (𝓝 (shotR L D (X:=x-y))) := by
  have he := ((appoint_as P.par h _ _).mp U).sub ((appoint_as P.par h _ _).mp V)
  refine Metric.tendsto_nhds.mpr fun a ha => bobbin_for.mpr ?_
  filter_upwards [travel_feast P.par.K.j L D (by rw [P.par.kJ]; norm_num) (zoomR P.par A)
    (zoom_grows P.par h) (zoom_pos P) w u (by simp_rw [rise_step]; exact he)
    (sub_ne_zero.mpr e) (a/2) (half_pos ha)] with s t
  filter_upwards [(thicken P p.up s).eventually t] with n g
  exact lt_of_le_of_lt (g (Vale.val_e ..) _) (half_lt_self ha)
omit p U V in
lemma diced_rescale (a : Side) (M : Jill.Male) (r j : ℕ) (u w : Cover) :
    diced r u w L D a j M = (r:ℂ)^6 * diced 1 u w L D a j M := by
  have h (L D : DirSpin) (u w : Cover) : dietary r u w L D a j M=(r:ℂ)^3 * dietary 1 u w L D a j M := by
    unfold dietary
    rw [in_transcript,in_transcript]
    unfold Emu.hopF
    push_cast; ring
  unfold diced; rw [h,h]; ring

omit U V in
lemma pair_photons {U V : ℕ → Cover} {r : ℕ → ℝ} (hr : ∀ i, 0 < r i) (hz : Tendsto r atTop atTop)
    (X : Gaia) (h : Tendsto (fun s => riseX (r s) (U s - V s)) atTop (𝓝 X)) (e : X ≠ 0) : Tendsto
    (fun z : ℕ × ℕ => acePower SU.group (magnify
      (P.par.V.L.H (P.run.uv (cutoff P (f z.2))-z.1)) (r z.1) (plaquette F)
      (plaquette G) (U z.1-V z.1) (More (orbitSize P f z))))
    bobbin (𝓝 (speckleV F G SU.group X)) := by
  refine Metric.tendsto_nhds.mpr fun ε e' => bobbin_for.mpr ?_
  filter_upwards [manifold F G P.par.K.top.clip P.par.V.W.parcel P.par.K.width (zero_lt_one.trans_le P.par.V.up)
    hr hz h e (ε/2) (half_pos e') SU.group] with s t
  filter_upwards [(thicken P p.up s).eventually t] with n p
  let v := P.run.uv (cutoff P (f n)) - s
  have g := P.par.V.L.roof v
  exact lt_of_le_of_lt (p _ g.1 (g.2.1 _)) (half_lt_self e')
end bought
end Rose
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

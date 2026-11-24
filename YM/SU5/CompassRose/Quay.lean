import YM.SU5.CompassRose.Warp
/-! # From the staff estimate to a true two-body Wake estimate on the Spine. 
   
    Includes scaling of both colors and generators, the actual unselected one-point subtraction,
    quantitative fees for its passage and the preservation of the appointment thinning.

    Each instrument in this estimate is MIXED. Does not claim a pure gauge or pure matter
    field at those resolution resources. These are Wake purchases toward the force test. -/
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

variable (P : Spine)
local notation "Y" => P.run
local notation "Λ" => P.par
local notation "K" => P.calibration
local notation "R" s:max A:max => sPow P.par s A
local notation "t₀" s:max => temp (hat (Λ).R.L (Λ).x s)
local notation "χ" s:max => WakeInvestment.chip (hat P.par.R.L P.par.x s) (-3)
local notation "ζ" A:max s:max => zoomR P.par A s

section geometries
variable {A I : ℝ} (X : Gaia)

structure LayoutBudget (A : ℝ) (x : Gaia) (W : ℕ → Staff) (r w : ℕ → ℕ) (F : PlaqAxes) (L : DirSpin) : Prop where
  spin : ∀ s, (W s).spin = L
  plane : ∀ s, (W s).face.2 = F
  spin_target : Appoint P.par A (fun s => (W s).u) x
  face_target : Tendsto (fun s => riseX (R s A) (W s).face.1) atTop (𝓝 x)
  credentials : ∀ s, (W s).Pays (r s) (w s)
  -- includes real clearance for its support and footprint. permits every larger microscope scale.
  approved : ∀ I > A, ∃ m : ℕ → ℕ, ∀ᶠ s in atTop,
    (m s:ℝ) ≤ R s I ∧ (w s:ℝ) ≤ R s I ∧
    ∀ N : Side, (W s).tenancy N (r s) Staff.clearance (m s) 0

/-- simplification: same-site FaceB·Current. (Look at budget separately for oriented moments.) -/
def visitor (x : Cover) (F : PlaqAxes) (L : DirSpin) : Staff :=
  { hub := nodeC x
    u := x
    face := (nodeC x,F)
    spin := L
    steps := []
    stop_at := rfl }

lemma issues (x : Cover) (F : PlaqAxes) (L : DirSpin) {m w : ℕ} (u : 4 ≤ m) :
    (visitor x F L).Pays m w := by
  let y := nodeC x
  refine ⟨Nat.zero_le w, fun i p => ?_, fun i p => pav_mono u ?_⟩
  · change i ∈ [y] at p
    rw [List.mem_singleton.mp p]; exact EmberWind.owns y m
  exact walk_pav y i (square F.val.1 F.val.2) (List.mem_toFinset.mp p)

/-- cover permission (permits even small aliased periods when used at those costs). -/
lemma localize (N : Side) (W : Staff) (d r : ℕ)
    (p : W.hub ∈ skyDeck 0 d) : W.tenancy N r Staff.clearance (d+(r+Staff.clearance+8)) 0 := by
  unfold Staff.tenancy Staff.gateS BlockP
  rw [← wrap_pav, ← map_zero (wrap (More N)), ← wrap_pav]
  apply image_subset_image
  intro i x
  refine (pav_v ..).2 fun j => ?_
  have ht := (pav_v ..).1 x j
  have hv := (pav_v ..).1 p j
  simp only [Pi.zero_apply] at *
  omega

/-- estimate when the staff hubs live in a bounded zoom-scaled box. -/
lemma hubLens (W : ℕ → Staff) (B : ℝ) (h : A < I) (p : 0 < I) (a : 0 < B) :
    ∃ d : ℕ → ℕ, ∀ᶠ s in atTop, (d s:ℝ) ≤ R s I /2 ∧
      (‖riseX (R s A) (W s).hub‖ ≤ B → (W s).hub ∈ skyDeck 0 (d s)) := by
  let m (s:ℕ) := ⌈B * R s A⌉₊
  refine ⟨m,?_⟩
  filter_upwards [budget_secondary P h (4*B),(sPower_pay P.par p).eventually_ge_atTop 4] with s Q H
  let U := R s A
  have hv : 0 < U := rungs_pos P s
  have he : 0 < B*U := mul_pos a hv
  have ht : (m s:ℝ) < B*U+1 := Nat.ceil_lt_add_one he.le
  change 4 * B * U < _ at Q
  refine ⟨by linarith only [ht,Q,H], fun S => (pav_v ..).2 fun i => ?_⟩
  let y := (W s).hub i
  have hg : |(y:ℝ)/U| ≤ B := (PiLp.norm_apply_le ..).trans S
  rw [abs_div, abs_of_pos hv] at hg
  have hy : (|(y:ℤ)|:ℤ) ≤ (m s:ℤ) := by
    have hx : |(y:ℝ)| ≤ (m s:ℝ) := ((div_le_iff₀ hv).mp hg).trans (Nat.le_ceil _)
    exact_mod_cast hx
  simpa only [zero_sub, Pi.zero_apply, zero_add] using abs_le.mp hy

lemma approved_visas {u : ℕ → Cover} (U : Appoint P.par A u X) (p : 0 < A)
    (F : PlaqAxes) (L : DirSpin) (r w : ℕ) (e : 4 ≤ r) :
    LayoutBudget P A X (fun s => visitor (u s) F L) (fun _ => r) (fun _ => w) F L := by
  let W s := visitor (u s) F L
  let C := ‖X‖ + 1
  have hC : 0 < C := add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
  have hx : ∀ᶠ s in atTop, ‖riseX (R s A) (W s).hub‖ ≤ C := by
    exact (show Tendsto _ _ _ from (show Tendsto (fun s => riseX (R s A) (W s).hub) atTop (𝓝 X) from U).norm).eventually
     (p := (· ≤ C)) (ge_mem_nhds (lt_add_one _))
  refine ⟨fun _ => rfl,fun _=>rfl,U,U,fun _=> issues _ _ _ e,fun I h => ?_⟩
  let d₀ := r + Staff.clearance + 8
  obtain ⟨m,t⟩ := hubLens P W C h (p.trans h) hC
  refine ⟨fun s=>m s+d₀,?_⟩
  filter_upwards [t,hx,(sPower_pay P.par (p.trans h)).eventually_ge_atTop (w:ℝ),
    (sPower_pay P.par (p.trans h)).eventually_ge_atTop (2*(d₀:ℝ))] with s t hx hw hd
  refine ⟨?_,hw,fun N => localize N (W s) (m s) r (t.2 hx)⟩
  push_cast; linarith only [t.1,hd]
end geometries

section pricing
abbrev grist (s : ℕ) (W : Staff) (r : ℕ) (t : ℝ) : Family K :=
  Papal.household K (W.rungWeave t r (t₀ s))
noncomputable def winding (A : ℝ) (s : ℕ) : ℝ := (R s A)^2 * (ζ A s:ℝ)^3
noncomputable def offers (A : ℝ) (s : ℕ) (W : Staff) (r : ℕ) (t : ℝ) : Family K :=
  (winding P A s:ℂ) • grist P s W r t

variable {A I t : ℝ} {F G : PlaqAxes} {L D : DirSpin} {x y : Gaia}
variable {W V : ℕ → Staff} {r w : ℕ → ℕ}
variable {f : ℕ → ℕ} {β : ℕ → ℝ} (p : Pools P f β) (pace : P.PhysicalWakeGram)
variable (U : LayoutBudget P A x W r w F L) (V' : LayoutBudget P A y V r w G D)
local notation "κ" s:max => κFix β s
local notation "ν" z:max => f ((z:ℕ×ℕ).2)
local notation "periodZ" z:max => Rose.period P (ν z)
local notation "cutoffZ" z:max => Rose.cutoff P (ν z)
local notation "Ξ" s:max z:max => Journey.sharp Y P.large s (periodZ z) (cutoffZ z)
-- helper
lemma gravel (t : ℝ) (W : Staff) (r s i k : ℕ) : Journey.sharp Y P.large s i k (grist P s W r t) =
    Journey.compass Y i k s (W.rungWeave t r (t₀ s) (side Y i s)) := by
  change Journey.compass Y i k s (expSrc Y s i P.large _) = _
  rw [grist, lift_book]

include U
lemma center_goods (s : ℕ) (t : ℝ) : InTest K true ((W s).skyRent (r s)) false (offers P A s (W s) (r s) t) ∧
    CovCover K (offers P A s (W s) (r s) t) := by
  let q := U.credentials s
  refine ⟨InTest.smul _ ((W s).letterBudget _ _ _ q),?_⟩
  have he := (W s).registration t (t₀ s) K q
  intro i g x; let c : ℂ := winding P A s
  simp only [offers,Pi.smul_apply,twist_scalar]
  exact congrArg (c • ·) (he i g x)

include pace p
lemma weave_price (h : 0 < A) : Tendsto
    (fun z : ℕ × ℕ => (Ξ z.1 z) (offers P A z.1 (W z.1) (r z.1) (κ z.1))) bobbin (𝓝 0) := by
  have hI : 0 < A+1 := by linarith
  obtain ⟨m,q⟩ := U.approved (A+1) (lt_add_one _)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (g := fun z : ℕ×ℕ => winding P A z.1 * χ z.1) (Eventually.of_forall fun _ => norm_nonneg _) ?_
    ((scaled_due P 2 3 h).comp Rose.runway)
  filter_upwards [paces P p pace hI, Rose.runway.eventually q] with z ht e
  obtain ⟨hv,hw,hB⟩ := e
  rw [offers, sharp_scale,gravel,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  have hx : 0 ≤ winding P A z.1 := mul_nonneg (sq_nonneg _) (pow_nonneg (Nat.cast_nonneg _) 3)
  rw [abs_of_nonneg hx]; exact mul_le_mul_of_nonneg_left
    (ht.single (U.credentials z.1) (hB _) (range_paid P p _) hv hw) hx

include V'
omit pace in
lemma wale_limit (h : 0 < A) (e : x ≠ y) :
    Tendsto (fun z : ℕ × ℕ => (winding P A z.1:ℂ)^2 *
      wale Y z.1 (periodZ z) (cutoffZ z) (W z.1) (V z.1) (κ z.1)) bobbin
      (𝓝 (shotR L D (X:=x-y)*speckleV F G SU.group (x-y))) := by
  let φ := fun z : ℕ×ℕ => gaugeCoupon (W z.1) (V z.1) (orbitSize P f z)
    ((Λ).V.L.H ((Y).uv (cutoffZ z)-z.1))
  have he : Tendsto (fun z : ℕ×ℕ => (R z.1 A:ℂ)^4 * φ z) bobbin (𝓝 (speckleV F G SU.group (x-y))) := by
    have hv := U.face_target.sub V'.face_target
    refine (pair_photons P p F G (U:=fun s=>(W s).face.1) (V:=fun s=>(V s).face.1)
      (r := fun i => R i A) (rungs_pos P) (sPower_pay P.par h) (x-y) ?_ (sub_ne_zero.mpr e)).congr ?_
    · simp_rw [rise_step]; exact hv
    intro z
    unfold φ gaugeCoupon; rw [U.plane,V'.plane]
    let r := R z.1 A; let N := orbitSize P f z
    let B := (Λ).V.L.H ((Y).uv (cutoffZ z)-z.1)
    let a := (W z.1).face.1; let b := (V z.1).face.1
    have h : magnify B r (plaquette F) (plaquette G) (a-b) (More N) =
        (r:ℂ)^4 * rimble (More N) B (wrap (More N) a, plaquette F) (wrap (More N) b, plaquette G) := by
      rw [magnify, rimflare (More N) B _ _ (a-b) (sub_zero _),
        rimflare (More N) B _ _ (a-b) (map_sub (wrap (More N)) a b).symm]
    change acePower _ (magnify B r (plaquette F) (plaquette G) (a-b) (More N)) = _
    rw [h]; unfold acePower r a b B orbitSize N; ring
  have hq := reach_normalized P p
  have ht := ((pair_spin P p U.spin_target V'.spin_target L D h e).mul
    ((Complex.continuous_ofReal.continuousAt.tendsto.comp hq).pow 2)).mul he
  push_cast at ht; rw [one_pow,mul_one] at ht
  apply ht.congr
  intro z
  let x := orbitSize P f z; let M := (pupil P z.1 (f z.2)).J.M
  change diced _ _ _ L D _ _ _ * _ ^ 2 * _ = _
  rw [wale, spinCoupon,diced_rescale L D x M]
  simp only [U.spin,V'.spin,winding,Function.comp_apply,φ]
  dsimp only [M,pupil,x,orbitSize,loom]; push_cast; ring

omit p U V' pace in
lemma tenancy_inc (N : Side) (X : Staff) (r d e l : ℕ) (p : e ≤ l) (h : X.tenancy N r d e 0) : X.tenancy N r d l 0 :=
  h.trans (Corona.halo_mono p (Subset.refl _))

lemma body_price (h : 0 < A) (e : x ≠ y) : Tendsto
    (fun z : ℕ × ℕ => (Ξ z.1 z) (offers P A z.1 (W z.1) (r z.1) (κ z.1) * offers P A z.1 (V z.1) (r z.1) (κ z.1)))
    bobbin (𝓝 (shotR L D (X:=x-y)*speckleV F G SU.group (x-y))) := by
  let B(u:ℕ×ℕ) := offers P A u.1 (W u.1) (r u.1) (κ u.1) * offers P A u.1 (V u.1) (r u.1) (κ u.1)
  let T (z:ℕ×ℕ) := (Ξ z.1 z) (B z)
  let d(z:ℕ×ℕ) : ℝ := winding P A z.1
  let J(z:ℕ×ℕ) := (d z:ℂ)^2 * wale Y z.1 (periodZ z) (cutoffZ z) (W z.1) (V z.1) (κ z.1)
  let a(z:ℕ×ℕ) := T z - J z
  have he : Tendsto a bobbin (𝓝 0) := by
    have hI : 0 < A+1 := by linarith
    obtain ⟨m,q⟩ := U.approved (A+1) (lt_add_one _)
    obtain ⟨m',q'⟩ := V'.approved (A+1) (lt_add_one _)
    rw [tendsto_zero_iff_norm_tendsto_zero]; apply squeeze_zero' (g := fun z : ℕ×ℕ => d z^2 * χ z.1) (Eventually.of_forall fun _=> norm_nonneg _) ?_ ?_
    swap
    · apply ((scaled_due P 4 6 h).comp Rose.runway).congr
      rintro ⟨s,n⟩; dsimp only [Function.comp,d,winding]; ring
    filter_upwards [paces P p pace hI,Rose.runway.eventually q,Rose.runway.eventually q'] with z ht q e
    let b := max (m z.1) (m' z.1); let x := orbitSize P f z
    obtain ⟨hv,hw,hB⟩ := q
    obtain ⟨hv',hw',hB'⟩ := e
    have hZ : (b:ℝ) ≤ R z.1 (A+1) := by unfold b; rw [Nat.cast_max]; exact max_le hv hv'
    have hK : 0 ≤ d z := mul_nonneg (sq_nonneg _) (pow_nonneg (Nat.cast_nonneg _) 3)
    change ‖T z-J z‖ ≤ _
    let Φ := W z.1; let Ψ := V z.1; let s := z.1
    let Y' := Φ.rungWeave (κ s) (r s) (t₀ s); let V'' := Ψ.rungWeave (κ s) (r s) (t₀ s)
    unfold T B; rw [offers,offers,Algebra.smul_mul_assoc, Algebra.mul_smul_comm,smul_smul,sharp_scale]
    change ‖_ * Journey.compass _ _ _ _ (expSrc Y s (periodZ z) P.large (Papal.household K (Y' * V''))) - _‖ ≤ _
    rw [lift_book]
    let k : ℂ := ↑(d z)
    change ‖k*k*_ - k^2*_‖ ≤ _
    rw [←pow_two, ←mul_sub_left_distrib,norm_mul,norm_pow]
    unfold k; rw [Complex.norm_real,Real.norm_of_nonneg hK]
    exact mul_le_mul_of_nonneg_left
      (ht.duo (U.credentials s) (tenancy_inc x _ _ _ _ b (le_max_left ..) (hB x)) (V'.credentials s)
        (tenancy_inc x _ _ _ _ b (le_max_right ..) (hB' x)) (range_paid P p _) hZ hw) (sq_nonneg _)
  have q := he.add (wale_limit P p U V' h e)
  rw [zero_add] at q
  exact q.congr fun z => sub_add_cancel (T z) (J z)
-- #print axioms wale_limit
end pricing
end Rose
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

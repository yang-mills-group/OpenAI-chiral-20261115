import YM.SU5.CompassRose.Shelves

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
open WakeInvestment Gleam Gleam.Wake
open scoped ContDiff

variable {I : Type*} [Fintype I] {W : Staff} {n : Side} {r e w : ℕ}
local notation "G" => SU.group
local notation "N" => ColorL
variable (X : Gleam.Wake.Vessel G (More n) I) (g : SU.group.ColorIndex → I)

-- pointwise accounting for one staff. read color bouquet at the enrolled curvature face.
def pickColor : (I → ℝ) →ₗ[ℝ] ColorL where
  toFun x := WithLp.toLp 2 fun i=> x (g i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
noncomputable def trailer (W : Staff) (n : Side) (g : SU.group.ColorIndex → I) := (wrapCurrent W.u W.spin 1 n).comp (pickColor g)

def tracked (V : Gleam.Wake.Vessel G (More n) I) (W : Staff) (g : SU.group.ColorIndex → I) : Prop :=
  ∀ i, V.view (g i) = (W.localFace n,i)
abbrev cartSize := (Fintype.card SU.group.ColorIndex:ℝ) -- uniform including for repeated purchases / variable I
private lemma pick_le (x : I → ℝ) : ‖pickColor g x‖ ≤ cartSize*‖x‖ := by
  let Y := pickColor g x
  let a := cartSize
  have hZ : 0 ≤ a := Nat.cast_nonneg _
  letI : Nontrivial SU.group.Color := Thera.yet_one.nontrivial_color
  have hd : 0 < SU.group.lieDim := by rw [Gauge.lieDim, ← SU.group.colorIso.finrank_eq]; exact Module.finrank_pos
  have hn : 1 ≤ a := by
    change (1:ℝ) ≤ Fintype.card (Fin SU.group.lieDim)
    rw [Fintype.card_fin]; exact_mod_cast hd
  apply le_of_pow_le_pow_left₀ (n:=2) (by decide) (mul_nonneg hZ (norm_nonneg _))
  rw [EuclideanSpace.real_norm_sq_eq]; apply le_trans (sum_le_sum (g:=fun _=> ‖x‖^2) ?_)
  · rw [sum_const, card_univ, nsmul_eq_mul, mul_pow]; exact mul_le_mul_of_nonneg_right (by nlinarith only [hn]) (sq_nonneg _)
  intro i _; let s := Y i; have ht : |s| ≤ ‖x‖ := norm_le_pi_norm x (g i)
  change _ ≤ _; apply le_trans _ (pow_le_pow_left₀ (abs_nonneg s) ht 2); rw [sq_abs]
lemma trunk {c : ℝ} (p : tracked X W g)(y : Pane n) : pickColor g (X.material c y) = W.cargoS n y c := by
  ext i; change c*(_ : ℝ) = _; unfold Vessel.ua Vessel.lens; rw [p]
  rfl

private lemma span_check (o : Seat n) (p : W.Pays r w) (q : W.tenancy n r Staff.clearance e o) :
    wrap (More n) (nodeC W.u) ∈ BlockP e o := q (Corona.halo_mono (show r ≤ r+_+8 from by omega)
        (Subset.refl _) ((p.withinP W n).2.1))
include g
private lemma pick_frame {o : Seat n}(p : W.Pays r w)(q : W.tenancy n r Staff.clearance e o) :
    Flora (modesIn _ (BlockP e o)) (Staff.regiment*cartSize) 2 1 (trailer W n g) := by
  let V := pickColor g
  let f := trailer W n g
  have he := span_check o p q
  refine ⟨f.toContinuousLinearMap.contDiff,fun K b x t => ?_,fun K b x y t u=>?_⟩
  · rw [pow_one]; refine (Staff.spin_at W.u W.spin (V x) _ _ he).buy le_rfl ?_; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ Staff.regge
    exact le_trans (pick_le g x) (mul_le_mul_of_nonneg_left t (Nat.cast_nonneg _))
  · rw [←map_sub,pow_one]; refine (Staff.spin_at W.u W.spin (V (x-y)) _ _ he).buy le_rfl ?_
    apply (mul_le_mul_of_nonneg_left (pick_le g (x-y)) Staff.regge).trans
    rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (mul_nonneg Staff.regge (Nat.cast_nonneg _)) b) (norm_nonneg _)

-- beacon cost using stronger power than scratch in the stencil error; same connector plank for every appearance.
-- formulated first at the geometry, not changing κ in any Step.
variable (a t α : ℝ) (o : Seat n)
local notation "ζ" => |a| *t
local notation "b0" => a
variable (p : W.Pays r w)(q : W.tenancy n r Staff.clearance e o) (u : tracked X W g)
omit g in
private lemma graphic (_ : W.Pays r w) (a t : ℝ) : Measurable (fun U:Pane n=> W.Beacon o (W.pearl a n r t U) U) := by
  let D := {U :Pane n| pingS t (W.gateS r n) U}
  let f(U:Pane n):= W.Beacon o (W.edgeBudget a n U) U
  have ht : Continuous f := (Staff.collarAd_cont G).comp
    (f:=fun U:Pane n=> (travel U o (Cube.march o (W.scope n) 1), W.edgeBudget a n U))
    (Continuous.prodMk (Wilson.continuous_travel _ _) (W.edge_budget_c a))
  apply (Eq.mpr ?_ (ht.measurable.indicator (show MeasurableSet D from ping_o.measurableSet)))
  apply congrArg (fun f:Pane n → ColorL => Measurable f)
  funext i; by_cases v:i∈D; · rw [Set.indicator_of_mem v]; unfold Staff.pearl; change pingS t _ i at v; rw [if_pos v]
  rw [Set.indicator_of_notMem v]; unfold Staff.pearl; change ¬ pingS t _ i at v; rw [if_neg v]; simp [Staff.Beacon]
local notation "ĉ" => Staff.regiment*(cartSize+(|a| *t))
local notation "C" => Staff.armRent (e:ℝ) α (|a| *t) (w:ℝ)
-- strip only true Orientation·constant. Not assuming cc3 identities.
include p q u
private lemma coast (D : Calibration) (m : Side) (hw : n=D.c m) (b : 0 ≤ t)(c : 0 ≤ α) :
    Hatch (BlockP e o) o (fun U => Tiny (BlockP e o) U α ∧ pingS t (W.gateS r n) U) (X.material a)
      (W.rungWeave a r t n) (trailer W n g) (fun U => wrapCurrent W.u W.spin 1 n (W.Beacon o (W.pearl a n r t U) U))
        (ĉ) (Staff.regiment * C) 2 1 := by
  let b₀:=Staff.regiment; let v(S:Pane n):= W.pearl a n r t S; let f:=wrapCurrent W.u W.spin 1 n; let φ(U):= W.Beacon o (v U) U; let F(U:Pane n) := f (φ U)
  have ht:0 ≤ |a| *t:=mul_nonneg (abs_nonneg _) b
  have hk: b₀*(|a| *t) ≤ ĉ :=mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Nat.cast_nonneg _)) Staff.regge
  have he:= span_check o p q
  have hu(y:N)(p:‖y‖≤|a| *t): Cadre (modesIn _ (BlockP e o)) 2 (ĉ) (f y):= (Staff.spin_at W.u W.spin y n _ he).buy le_rfl ((mul_le_mul_of_nonneg_left p Staff.regge).trans hk)
  have hy(y z:N) (p:‖y-z‖≤C): Cadre (modesIn _ (BlockP e o)) 2 (Staff.regiment*C) (f y-f z):=by rw [←map_sub]; exact (Staff.spin_at W.u W.spin _ _ _ he).buy le_rfl (mul_le_mul_of_nonneg_left p Staff.regge)
  refine ⟨deckVenue W a p t D m hw q,W.oneVox a r t n,fun x=>((W.sizing p a x b q)).buy le_rfl hk,
    f.toContinuousLinearMap.continuous.measurable.comp (graphic o p a t), ?_, fun x=> hu _ ((Gauge.norm_adjoint ..).le.trans (W.pearl_le p _ b a)),
    (pick_frame g p q).extra (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ht) Staff.regge),?_,?_,?_⟩
  · intro g x
    change f (W.Beacon _ _ _) = _
    rw [W.dockGauge,Staff.Beacon.moves]
    exact current_cov W.u W.spin 1 (φ x) (1,1) (fun _=> g o)
  · intro i h; change Cadre _ _ _ (f (pickColor g _)); rw [trunk X g u]; exact hu _ (W.keeper_car p i h.2 a).1
  · intro x h; rw [W.onMark]; apply hy; rw [norm_sub_rev]; apply le_trans (W.pearl_cost _ p q a h.2 h.1 c).2
    unfold Staff.armRent; have h:=SU.group.colorScale_pos; nlinarith only [mul_nonneg (mul_nonneg (mul_nonneg h.le (Nat.cast_nonneg (α:=ℝ) w)) c) ht]
  · intro i h; change Cadre _ _ _ (f (φ i)-f (pickColor g _)); rw [trunk X g u]; apply hy; apply (norm_sub_le_norm_sub_add_norm_sub _ (W.pearl a n r t i) _).trans; unfold Staff.armRent; obtain ⟨p,p'⟩:=W.pearl_cost i p q a h.2 h.1 c; exact (add_le_add p' p).trans_eq (by ring)
omit p q u g
private lemma shrink_hatch {I:Type*}[Fintype I]{B:Support (More n)} {Xx D:Pane n → Prop}{U: Pane n → I → ℝ}
  {W : Mark n}{F}{D'}{c b : ℝ}{d m:ℕ} (h:Hatch B o Xx U W F D' c b d m)(t:∀ x,D x→Xx x): Hatch B o D U W F D' c b d m :=
  ⟨h.first,h.bonds,h.full,h.texture,h.global,h.sample,h.promise,fun x a=>h.mantle x (t x a),fun x a=>h.crop x (t _ a),fun x a=>h.ends x (t x a)⟩

section trajectory
variable (P : Spine) (v : ℕ → ℕ) (S : Foyer P v)
local notation "pᵥ" z:max => Rose.period P (v ((z:ℕ×ℕ).2))
local notation "cᵥ" z:max => Rose.cutoff P (v ((z:ℕ×ℕ).2))
local notation "O" z:max => orbitSize P v z
local notation "Y" => P.run
local notation "R" s:max A:max => sPow P.par s A
local notation "τ" z:max => hat P.par.R.L P.par.x ((z:ℕ×ℕ).1)
lemma skyline_easy : Deep P fun z : ℕ×ℕ => skyline (τ z) := Loan.turns (a':=-8) (a:=-120000) (by norm_num) (Loan.fixed _ 0)
-- helper
lemma pedestal_bills (u : LaunchFee P v S) : Easy P (fun z=> |S.pedestal z| * temp (τ z)) := by
  let K := Jewel.grass 1
  apply Loan.of_felt (Easy.rungs K) (Eventually.of_forall (fun _=> mul_nonneg (abs_nonneg _) (Work.E04.temp_nonneg _)))
  filter_upwards [u.lives,Rose.runway.eventually (CircusPrice.ready P.par 1 1 zero_le_one zero_lt_one),
    Rose.runway.eventually ((sPower_pay P.par (A:=K) (by unfold K grass; linarith)).eventually_ge_atTop 1)] with z a b c
  have hb := (b.tally (S.pedestal z) a.2.2).1
  rw [one_mul] at hb
  change 1 ≤ R z.1 K at c
  nlinarith only [hb,c]

variable {A : ℝ}
def poses (A : ℝ) : Threading := fun z => (R z.1 A)^2 * (zoomR P.par A z.1:ℝ)^3
lemma scarf (p : 0 < A) : Easy P (poses P A) :=
  Easy.mul (Loan.pow (Easy.rungs A) 2) (Loan.pow (Easy.zoom p) 3)
lemma chromatic_bills (p : 0 < A) : Easy P (fun z=> ‖((poses P A z:ℝ):ℂ)‖) := by
  apply Loan.of_coat (scarf P p); apply Eventually.of_forall; intro i
  rw [Complex.norm_real, Real.norm_eq_abs,abs_abs]
lemma launch_granted {β:ℕ→ℝ} (T: Pools P v β)
    {W : ℕ×ℕ→Staff}{U : ∀ z:ℕ×ℕ,(G).ColorIndex → S.faces z}{r : ℕ×ℕ→ℕ}
    (e w : ℕ×ℕ→ℕ) (h:Easy P fun z => (e z:ℝ))(h':Easy P fun z=>(w z:ℝ))
    (x : LaunchFee P v S)(b0' : S.threshold < 1)
    (l : ∀ᶠ z in bobbin, tracked (S.ship z) (W z) (U z) ∧ S.B z=BlockP (e z) (S.anchor z) ∧
      (W z).Pays (r z) (w z) ∧ (W z).tenancy (O z) (r z) Staff.clearance (e z) (S.anchor z)) :
   Board P v S (fun z=> trailer (W z) (O z) (U z))
     (fun z=>(W z).rungWeave (S.pedestal z) (r z) (temp (τ z)) (O z)) 2 1 := by
  let L( z :ℕ×ℕ) := temp (τ z); let K(z :ℕ×ℕ) := |S.pedestal z| * L z
  let C' : ℝ := 2*SU.group.colorScale
  let A : Threading := fun z=> Staff.regiment*(cartSize+K z)
  let E : Threading := fun z=> Staff.regiment*Staff.armRent (e z) (skyline (τ z)) (K z) (w z)
  have hx := pedestal_bills P v S x
  refine ⟨A,E,Easy.mul (Loan.constant Staff.regiment P) ((Loan.constant cartSize P).add hx),?_,?_⟩
  · exact Easy.deep (Loan.constant Staff.regiment P) (Easy.deep' hx (Easy.deep (Easy.mul (Loan.constant C' P) (Loan.add h' (Easy.mul (Loan.constant 4 P) h))) (skyline_easy P)))
  filter_upwards [l,(bobbin_for (p:=fun z=> Ferry Y z.1 (pᵥ z) (cᵥ z))).mpr (Eventually.of_forall fun s=> finance P T s)] with z p t
  obtain ⟨p,a,b,d⟩:=p; let i:= pᵥ z; let k:= cᵥ z; let s:=z.1; let D:= S.anchor z; let W':= W z; let η:= (pupil P s (v z.2)).p.threshold; let Φ:= L z; let y:= S.pedestal z
  have hw := coast (S.ship z) (U z) y Φ (skyline (τ z)) D b d p P.calibration (momentm Y i s) (terrain Y P.large ((Y).ir i) s).symm (Work.E04.temp_nonneg _) (chip_pos ..|>.le)
  unfold drawn; rw [a]; refine ⟨_,shrink_hatch D hw (fun x h=>⟨h.1,?_⟩)⟩
  have he : η=Φ := (congrArg BudgetPoint.threshold (Papal.prices_plot Y s i k t.enters).1).trans (((Y).meter.boot s).1)
  have hv:S.threshold*η<η:= mul_lt_of_lt_one_left (pupil P s (v z.2)).p.threshold_pos b0'
  exact W'.passage x D d h.2 (hv.trans_eq he)
end trajectory
end Rose
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

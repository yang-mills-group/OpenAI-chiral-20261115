import YM.CF.Vp929.Budget.Arith
import YM.CF.Continuum.Block
import YM.CF.Continuum.Billhead
import YM.CF.Roots.Bind
import YM.CF.Py.Costs
import YM.CF.Vp929.Analysis.Integrate

/-! Per-site estimate on complex records and holomorphy. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief VolumeRate
open scoped Mew
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
variable {d h x a v t : ℝ} {m n B : Side} {U : Grasp V.U B d} {W : GivenX V U}
    {p : BudgetPoint} {Z : PathData SU.group} {F : Corr n} {G : Clip} {I : Interest n}
lemma inc_complex {F : RegBudget n} (u : IncX primeU F p h a) (c : ℂ) : IncX primeU (c • F) p h (‖c‖*a) := by
  obtain ⟨f,t,z⟩:= u.weight; refine ⟨⟨‖c‖ • f,fun X=> Roots.súe X _ (t X) _,fun x=>?_⟩,fun _ v=>v.elim⟩
  refine (mul_le_mul_of_nonneg_left (z x) (norm_nonneg c)).trans' (le_of_eq ?_)
  rw [mul_sum]; apply sum_congr rfl; intro i _; split <;> simp only [mul_zero,BudgetPoint.mass,Pi.smul_apply,smul_eq_mul] <;> ring
lemma dark_complex {F : ForceBudget n} (u : Dark primeU F p h a) (c : ℂ) : Dark primeU (c • F) p h (‖c‖*a) := by
  obtain ⟨f,t,z⟩:= u.weight; refine ⟨⟨‖c‖ • f,fun X=> Roots.dúe X _ (t X) _,fun x=>?_⟩,fun _ v=>v.elim⟩
  refine (mul_le_mul_of_nonneg_left (z x) (norm_nonneg c)).trans' (le_of_eq ?_)
  rw [mul_sum]; apply sum_congr rfl; intro i _; split <;> simp only [mul_zero,BudgetPoint.mass,Pi.smul_apply,smul_eq_mul] <;> ring
protected lemma Cost.lot (u : Cost p h a F) (b : ℝ) (v : ℂ) : LotR (construct p Z G I b F v) h a a :=
  ⟨⟨u.inc.weight,fun _ v=>v.elim⟩,rfl,⟨u.dark.weight,fun _ v=>v.elim⟩⟩
lemma lotC {F : Pair (Corr n)} (u : Both (Cost p h a) F) (b : ℝ) (v : ℂ) : LotR (construct p Z G I b (Pair.plus F) v) h (a+a) (a+a) := by
  have u₁:= Cost.inc u.1; have u₂:=Cost.inc u.2; have v₁:= Cost.dark u.1; have v₂:=Cost.dark u.2
  refine ⟨ Larch.add_v p _ _ ⟨u₁.weight,fun _ v=> v.elim⟩ ?_,rfl, Fixed.Voltage.cloudy p primeU ⟨v₁.weight,fun _ v=>v.elim⟩ ?_ ⟩
  · change IncX primeU (Complex.I • F.2.1) p h a; simpa only [Complex.norm_I,one_mul] using inc_complex (u := (show IncX primeU _ _ _ _ from ⟨u₂.weight,fun _ v=>v.elim⟩)) Complex.I
  change Dark primeU (Complex.I • F.2.2) p h a; simpa only [Complex.norm_I,one_mul] using dark_complex (show Dark primeU _ _ _ _ from ⟨v₂.weight,fun _ v=>v.elim⟩) Complex.I
local notation "N" => mid m B
lemma paths_nonneg (V : Grace K R L) : 0 ≤ K.top.paths := by
  obtain ⟨t,h,q⟩:= (V.L.mood 0).rows (⟨(0,1), by decide⟩); exact le_trans (tsum_nonneg t) q
def taxPart (V : Grace K R L) (p : BudgetPoint) (b : ℝ) := b*(K.top.paths*p.threshold^3+K.top.paths*p.threshold^4)+V.W.bar*p.threshold^2
lemma tax_price (V : Grace K R L) {p : BudgetPoint} (n : Side) {b y : ℝ} (s : b ≤ y) : Graph.taxY (More n) b p.threshold K.top.paths V.W.bar ≤ taxPart V p y * sites n := by
  have h:=p.threshold_pos; let c:= K.top.paths; have hc:0≤c:=paths_nonneg V; have he:0 ≤ c*p.threshold^3+c*p.threshold^4:=by positivity
  unfold Graph.taxY taxPart; let m:= sites n; change b*(m*_)+m*_ ≤ _*m;
  linarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right s he) (zero_le_one.trans (sites_pos n))]
def earnings (W : GivenX V U) (p : BudgetPoint) (b a : ℝ) := taxPart V p b + (4*cashU W.C+(3*a)*2^4+180*45*6*cashU W.C)/16
lemma extensive (W : GivenX V U) {I : Interest N} (hp : InterestX W.C _ I) {S : Scree.Loom N} {v : ℝ} {k : ℕ} (u : Roof _ v d k S) (l : ℕ)
    (e : U.roundZ ≤ (N).val) (hh : 1 ≤ h) {F : Corr N} (β : ℝ) (y : ℂ) (ht : LotR (construct p (V.L.path l) K.top.clip I β F y) h a a)
    (hb : 0 ≤ β) (hz : β ≤ x) (b : Orbit N) : ‖field U (construct p (V.L.path l) K.top.clip I β F y) S b‖ ≤ Real.exp (earnings W p x a * sites (mid m B)) := by
  have H:= Window.extensive_price _ S u U e (frostQ ht (zero_le_one.trans hh) hp) (V.L.mood l) (level_p _).le hh (cash_v _) hb b; rw [←Real.exp_add] at H
  apply H.trans; apply Real.exp_monotone; refine (add_le_add_left (tax_price V N (p:=p) hz) (Window.flagBill N a a (cashU W.C))).trans_eq ?_
  rw [Window.flagBill_eq]; unfold earnings sites; change _+_= _ * ((((mid m B).val*2:ℕ):ℝ)^4); simp only [More]; push_cast; ring
lemma denInt (W : GivenX V U) {I : Interest N} {S : Scree.Loom N} {v : ℝ} {k : ℕ} (u : Roof _ v d k S) (l : ℕ)
    (e : U.roundZ ≤ (N).val) {F : Corr N} (β : ℝ) (y : ℂ) (ht : LotR (construct p (V.L.path l) K.top.clip I β F y) h a a) : Envelope (denZ (construct p (V.L.path l) K.top.clip I β F y) U S) :=
  Girt.sailW _ (ward_m (V.L.mood l) ht) W.pearl V.note W.health (by have he:=V.L.lobby; have hh:=R.order_cut; omega) k S u e
lemma cfield_bound (W : GivenX V U) {I : Interest N} (hp : InterestX W.C _ I) {S : Scree.Loom N} {k : ℕ} (u : Roof _ v d k S) (l : ℕ)
    (e : U.roundZ ≤ (N).val) (hh : 1 ≤ h) {F : Pair (Corr N)} (β : ℂ) (ht : Both (Cost p h a) F)
    (hb : 0 ≤ β.re) (hz : β.re ≤ x) (b : Orbit N) : ‖cfield p U I l S F β b‖ ≤ Real.exp (earnings W p x (a+a) * sites (mid m B)) := by
  have H:= extensive W hp u l e hh _ 0 (lotC ht _ _) hb hz b
  unfold field at H; unfold cfield; rw [norm_smul,Complex.norm_exp]; change _ * _ ≤ _
  simpa [Complex.mul_re,Complex.mul_im, construct] using H
open Push.BetaTransport in
lemma cfield_meas (W : GivenX V U) {I : Interest N} {S : Scree.Loom N} {k : ℕ} (u : Roof _ v d k S) (l : ℕ)
    (e : U.roundZ ≤ (N).val) {F : Pair (Corr N)} (β : ℂ) (ht : Both (Cost p h a) F) : Measurable (cfield p U I l S F β) := by
  unfold cfield; have H : Measurable (fun i : Orbit N=> kinetic (V.L.path l) K.top.clip p i.1) := (kinetic_env (P:=p) (n:=More N) (V.L.mood l)).1.comp (β:=Pane N) (α:=Orbit N) measurable_fst
  refine Measurable.smul (Complex.continuous_exp.measurable.comp (measurable_const.mul (Complex.continuous_ofReal.measurable.comp H))) (denInt W u l e _ 0 (lotC ht _ _)).1
open Push.BetaTransport in
lemma cfield_holo {I : Interest N} {S : Scree.Loom N} {l : ℕ} {U' : Set ℂ} {F : ℂ → Pair (Corr N)} (b : ℂ → ℂ)
    (u : HoloCorr U' F) (t : DifferentiableOn ℂ b U') (p : BudgetPoint) (x : Orbit N) : DifferentiableOn ℂ (fun z=> cfield p U I l S (F z) (b z) x) U' := by
  let f:= V.L.path l; let Z:= (S x); let d:= -((f.inChannels K.top.clip p 0 x.1):ℂ) - Pec.pigment I.I Z; let A:= fun z:ℂ=> construct p f K.top.clip I (b z).re (Pair.plus (F z)) 0
  let c:ℂ:=(kinetic f K.top.clip p x.1:ℝ); let L:= (tale_L (relV U I Z)).comp (tankL (spar K.j I.M Z))
  have he(z) : cfield p U I l S (F z) (b z) x = Complex.exp (d - b z*c) • L ((A z).board x) := by
    unfold cfield denZ; rw [smul_smul,←Complex.exp_add]; refine congrArg (fun v : ℂ=> Complex.exp v • L ((A z).board x)) ?_; unfold d c GramM.betaL GramM.H0; dsimp [construct,f,Z]; rw [channels_split]; push_cast; linear_combination -((kinetic (V.L.path l) K.top.clip p x.1:ℝ):ℂ)*Complex.re_add_im (b z)
  simp_rw [he]; refine DifferentiableOn.smul ((differentiableOn_const _).sub (t.mul_const c) |>.cexp) (L.differentiable.comp_differentiableOn ?_)
  unfold GramM.board; dsimp only [A, construct]; simp_rw [Vale.still_Footprint,add_zero]; refine DifferentiableOn.mul (Differentiable.comp_differentiableOn (fun x=>(NormedSpace.exp_analytic x).differentiableAt) ?_) ?_
  · unfold exponentL numbE; refine DifferentiableOn.fun_sum fun i _=> ?_; by_cases h:x.1∈ {U|pingS p.threshold i.val.2 U}; · simp_rw [Set.indicator_of_mem h]; exact (u.1 i x.1).1
    simp_rw [Set.indicator_of_notMem h]; exact differentiableOn_const _
  unfold fueled; apply DifferentiableOn.fun_sum; intro i _; split_ifs with h
  · unfold clamp; apply DifferentiableOn.fun_finsetProd; intro j _; split_ifs; exact (u.2 j x).1; exact differentiableOn_const _
  exact differentiableOn_const _
lemma c_beam (W : GivenX V U) {I : Interest N} (hp : InterestX W.C _ I) {S : Scree.Loom N} {k : ℕ} (u : Roof _ v d k S) (l : ℕ)
    (e : U.roundZ ≤ (N).val) (hh : 1 ≤ h) {U' : Set ℂ} (ho : IsOpen U') {F : ℂ → Pair (Corr N)} (b : ℂ → ℂ)
    (f : HoloCorr U' F) (t : DifferentiableOn ℂ b U') (p : BudgetPoint) (ht : ∀ z∈U', Both (Cost p h a) (F z) ∧ 0 ≤ (b z).re ∧ (b z).re ≤ x) :
    let g (z : ℂ) := cpartition p U I l S (F z) (b z); DifferentiableOn ℂ g U' ∧ ∀ z∈U', ‖g z‖ ≤ Real.exp (earnings W p x (a+a)*sites (mid m B)) := by
  intro g; let K:= Real.exp (earnings W p x (a+a)*sites (mid m B)); let L:= innerSL ℂ (mateK N); let G(z:ℂ):= fun y=> L (cfield p U I l S (F z) (b z) y)
  have hm z (hz:z∈U') : AEStronglyMeasurable (G z) (city _):=L.continuous.comp_aestronglyMeasurable ((cfield_meas W u l e (b z) (ht z hz).1).aestronglyMeasurable)
  have hB z (hz:z∈U') (i) : ‖G z i‖ ≤ K:= (norm_inner_le_norm (mateK N) (cfield p U I l S (F z) (b z) i) (𝕜:=ℂ)).trans (by rw [(tickB N).2,one_mul]; exact cfield_bound W hp u l e hh (b z) (ht z hz).1 (ht z hz).2.1 (ht z hz).2.2 _)
  refine ⟨integrate_holo (μ:=city _) (F:=G) (v:=fun _=> K) ho (Eventually.of_forall fun i=> ⟨L.differentiable.comp_differentiableOn (cfield_holo b f t p i),fun z v=>hB z v i⟩) hm (integrable_const _),fun z hz=>?_⟩
  exact le_trans (norm_integral_le_of_norm_le (integrable_const K) (Eventually.of_forall fun i=> hB z hz i)) (le_of_eq (by rw [integral_const,probReal_univ,one_smul]))
end YM.CF.Py.Rate

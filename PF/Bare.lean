import SU5SatinProgressNovember7B
set_option autoImplicit false
set_option maxHeartbeats 380000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
/-!
# Common bare prescription on precisely the EB.1–EB.6 coordinates

Following the construction notes, with support iteration rather than
independent advancement of two operands. Compass/partition/cap laws of the project;
the pair index in the *intermediate* calculations does not see a new Grasp or phase.
-/
namespace PureForce
variable (P : Spine)

def iPath (u : ℕ) := P.period (P.projection.rows u)
def kPath (u : ℕ) := P.cutoff (P.projection.columns u)

local notation "Y" => P.run
local notation "Λ" => P.par
local notation "Kc" => P.calibration
open Reconstruction

def depth (u : ℕ) := (Y).uv (kPath P u)
def periodSize (u : ℕ) : ℕ := ((Y).ir (iPath P u)).val

lemma iPathStrict : StrictMono (iPath P) := P.law.pick.grow_i.comp P.history.growsA
lemma kPathStrict : StrictMono (kPath P) := P.law.pick.grow_k.comp P.history.growsB
lemma depthStrict : StrictMono (depth P) := (Y).uv_grows.comp (kPathStrict P)
lemma periodStrict : StrictMono (periodSize P) := (Y).ir_grows.comp (iPathStrict P)
lemma path_limits : Tendsto (depth P) atTop atTop ∧ Tendsto (periodSize P) atTop atTop :=
  ⟨(depthStrict P).tendsto_atTop,(periodStrict P).tendsto_atTop⟩

def gramAt (i k s : ℕ) := (((Y).voyage i).X ((Y).uv k)).gram s
def eff (i k s : ℕ) := (gramAt P i k s).beta

lemma terminal {K : P.Register} {L M : ℝ} {X : Supplier} (h : uniform P K X L M) (i k : ℕ) :
    eff P i k 0 = (Λ).x := P.terminalBeta K h _ _

/-- Actually positive for all i,k and all s below or equal to top. -/
lemma eff_pos (i k s : ℕ) (t : s ≤ (Y).uv k) : 0 < eff P i k s := by
  have he : (1:ℝ) ≤ hat (Λ).R.L (Λ).x s := (Y).oneP.trans (Vale.crown ..)
  have hp := ((Papal.prices_plot (Y) s i k t).2.2.2.1).1
  exact (half_pos (zero_lt_one.trans_le he)).trans_le hp

def bareBeta (v : ℕ) : ℝ := by
  classical
  exact if h : ∃ u, depth P u = v then
    eff P (iPath P h.choose) (kPath P h.choose) v else 1
@[simp] lemma beta_match (u : ℕ) : bareBeta P (depth P u) = eff P (iPath P u) (kPath P u) (depth P u) := by
  have h : ∃ u', depth P u' = depth P u := ⟨u,rfl⟩
  have he : h.choose = u := (depthStrict P).injective h.choose_spec
  rw [bareBeta,dif_pos h,he]
lemma beta_pos (v : ℕ) : 0 < bareBeta P v := by
  unfold bareBeta
  split <;> rename_i h
  · apply eff_pos; change v ≤ depth P h.choose; exact le_of_eq h.choose_spec.symm
  exact zero_lt_one

variable (i k : ℕ)
local notation "Nv" => side P.run i (P.run.uv k)

/-- EB.2 integrand at any bare inverse coupling, in the actual regulator data
(one Grasp, phase ket and 45 slots, same P.par, true empty-flags indicator). -/
def bareWeight (π : ℝ) (A : Evaluation (side P.run i (P.run.uv k))) (U : Pane (side P.run i (P.run.uv k))) :=
  inner ℂ (Dial.mateK (Nv)) (acts (A U) (Vale.capP («K»:= (Λ).K) (Λ).U π ((Y).meter.a ((Y).uv k)) U))

lemma usesWeight (A : Evaluation (side P.run i (P.run.uv k))) :
    bareAmplitude (Y) i k A = bareWeight P i k (eff P i k ((Y).uv k)) A := rfl

/-- This, NOT compass income unweighted away from the chosen path, is the
common-bare law. -/
abbrev W (A : Evaluation (side P.run i (P.run.uv k))) :=
  ∫ U, bareWeight P i k (bareBeta P ((Y).uv k)) A U ∂prior SU.group (More (Nv))

abbrev tilt (target source : ℝ) (U : Pane (side P.run i (P.run.uv k))) :=
  Complex.exp ( - (↑((target-source)*Vale.basicP (Λ).K.top.clip U) : ℂ))
lemma tilted (target source : ℝ) (A : Evaluation (side P.run i (P.run.uv k))) :
    bareWeight P i k target A = bareWeight P i k source (fun U=>tilt P i k target source U • A U) := by
  funext U; unfold bareWeight tilt capP
  by_cases h : flags ((Y).meter.a ((Y).uv k)).threshold U = ∅
  · simp only [Set.indicator_of_mem (show U∈ {U : Pane (Nv) | flags ((Y).meter.a ((Y).uv k)).threshold U = ∅} from h)
      ]
    rw [act_smul]
    simp only [map_smul, smul_smul, ← Complex.exp_add]
    have hx : -(↑(target*Vale.basicP (Λ).K.top.clip U):ℂ)= (-(↑((target-source)*Vale.basicP (Λ).K.top.clip U):ℂ)) + (-(↑(source*Vale.basicP (Λ).K.top.clip U):ℂ)) := by push_cast; ring
    rw [hx]
  rw [Set.indicator_of_notMem (show U ∉ {U : Pane (Nv) | flags ((Y).meter.a ((Y).uv k)).threshold U = ∅} from h),
     Set.indicator_of_notMem (show U ∉ {U : Pane (Nv) | flags ((Y).meter.a ((Y).uv k)).threshold U = ∅} from h)]
  simp only [map_zero]

private lemma compactEnvelope {n : Side} (f : Pane n → ℂ) (h : Continuous f) : Envelope f := by
  obtain ⟨c,hc⟩ := bddAbove_def.mp (isCompact_range h.norm).bddAbove
  exact ⟨h.measurable,c,fun x=>hc _ ⟨x,rfl⟩⟩

lemma tiltEnvelope (target source : ℝ) (A : Evaluation (side P.run i (P.run.uv k))) (h : Envelope A) :
    Envelope (fun U => tilt P i k target source U • A U) := by
  let f := tilt P i k target source
  have hf : Envelope f := compactEnvelope _ <|
    Complex.continuous_exp.comp <| Continuous.neg <| Complex.continuous_ofReal.comp <|
      continuous_const.mul (Nova.ren_c _)
  obtain ⟨c,hc⟩:=hf.cost; obtain ⟨d,hd⟩:=h.cost
  exact ⟨hf.meas.smul h.meas, c*d,fun U=> norm_smul (f U) (A U) ▸
    mul_le_mul (hc _) (hd _) (norm_nonneg _) ((norm_nonneg _).trans (hc U))⟩
local notation "μ" => prior SU.group (More (side P.run i (P.run.uv k)))
lemma bare_integrable (q : ((Y).voyage i).kick ≤ k) (π : ℝ) (A : Evaluation (side P.run i (P.run.uv k))) (h : Envelope A) :
    Integrable (bareWeight P i k π A) (μ) := by
  let A' := fun U=> tilt P i k π (eff P i k ((Y).uv k)) U • A U
  rw [tilted P i k π (eff P i k ((Y).uv k)), ←usesWeight]
  have hl : Envelope (toMark A') := Env.along (tiltEnvelope P i k _ _ _ h) measurable_fst
  exact (compassIncome (Y) i k hl q).1

set_option quotPrecheck false
set_option maxHeartbeats 48000
local notation "w" => tilt P i k (eff P i k ((Y).uv k)) (bareBeta P ((Y).uv k))
local notation "Zv" => partitionZ (gramAt P i k (P.run.uv k)) (Λ).U (((Y).voyage i).CapeT ((Y).uv k))

lemma partitionW (p : ((Y).voyage i).kick ≤ k) :
    (Zv) = W P i k (fun U=> (w) U • 1) := by
  unfold gramAt
  rw [partitionIncome (Y) i k p|>.2, usesWeight, tilted _ _ _ _ (bareBeta P ((Y).uv k))]; rfl

lemma compassW {F : Mark (side P.run i (P.run.uv k))} (h : Envelope F) (p : ((Y).voyage i).kick ≤ k) :
    W P i k (fun U=> (w) U • 1) ≠ 0 ∧
    Journey.compass (Y) i k ((Y).uv k) F = W P i k (fun U=> (w) U • F (U,U)) / W P i k (fun U=> (w) U • 1) := by
  have hu := compassIncome (Y) i k h p
  simp only at hu
  rw [usesWeight,usesWeight, tilted _ _ _ _ (bareBeta P ((Y).uv k)) 1,
    tilted _ _ _ _ (bareBeta P ((Y).uv k)) (diagMark F)] at hu -- ordering
  exact hu.2

lemma compassWpath (u : ℕ) {F : Mark (side P.run (iPath P u) (depth P u))}
    (h : Envelope F) (p : ((Y).voyage (iPath P u)).kick ≤ kPath P u) :
    W P (iPath P u) (kPath P u) 1 ≠ 0 ∧
    Journey.compass (Y) (iPath P u) (kPath P u) (depth P u) F =
    W P (iPath P u) (kPath P u) (diagMark F) / W P (iPath P u) (kPath P u) 1 := by
  unfold W; change (∫ U, bareWeight P _ _ (bareBeta P (depth P u)) 1 U ∂_) ≠ 0 ∧ _ -- simp beta both via change at path beta
  have eq : bareBeta P (P.run.uv (kPath P u)) = _ := beta_match P u
  have hx(A:Evaluation (side P.run (iPath P u) (depth P u))) := usesWeight P (iPath P u) (kPath P u) A
  simp only [eq,depth,←hx]; exact (compassIncome (Y) _ _ h p).2

/-- Actual iterative support up to v (retain singlet if started with it).
Uses the real Loom assignment each s. -/
lemma compassAsc (s t : ℕ) (hs : s ≤ t) (hq : Tapestry.Pay (Y) t i k)
    (F : Mark (side P.run i s)) (S : Finset Cover) (h : AtSupport false (Satin.region S _) F) :
    ∃ A : Mark (side P.run i t),
      AtSupport false (Satin.region ((followBox («Λ»:=P.par) (l:=P.width))^[t-s] S) _) A ∧
      (covariant F → covariant A) ∧
      Journey.compass (Y) i k s F= Journey.compass (Y) i k t A := by
  induction t, hs using Nat.le_induction with
  | base => exact ⟨F,by simpa using h, id,rfl⟩
  | succ n e ih =>
    obtain ⟨A,hA,pc,hf⟩:= ih ⟨hq.1,(Nat.le_succ n).trans hq.2⟩
    have hc:Satin.PairIdx (Y) n i k:= ⟨hq.1,hq.2⟩
    refine ⟨Tapestry.ascender (Y) n i k A, ?_,fun x=>Tapestry.ascendGauge (Y) n i k hc hA (pc x), hf.trans ?_⟩
    · convert Tapestry.ascendSupport (Y) n i k _ hc hA using 2
      rw [show n+1-s=n-s+1 from by omega, iterate_succ_apply']
    exact Tapestry.partake (Y) n i k hc (hA.mono (subset_univ _))
lemma chart (s : ℕ) (S : Finset Cover) {F : P.Test} (p : InTest (Kc) true S false F.val) :
    Tendsto (fun u=> Journey.compass (Y) (iPath P u) (kPath P u) s (exhibit (Y) P.large s (iPath P u) F.val)) atTop (𝓝 (P.E s F.val)) := by
  simp_rw [←Tapestry.actualRead]
  apply Metric.tendsto_nhds.mpr; intro ε hp
  obtain ⟨v,hv⟩ := valuation (Y) P.large p
  obtain ⟨_,_,hq⟩ := P.history.implements s S
  have hn: 0 ≤ v := pay_nonneg (show pay F.val v from hv)
  let t:= ε/(v+1); have ht:0<t:=by dsimp[t];positivity
  filter_upwards [hq t ht] with u hu
  rw [dist_eq_norm]
  refine ((hu _ p _ hv).2.2.2.2.1).trans_lt ?_
  have he:t*(v+1)=ε:= div_mul_cancel₀ _ (by positivity)
  linarith

/-- Height-s joint Mark with its actual internal levels, read against the one
bare prescription and with a cutoff *singlet* sensor, limit on exactly EB.6's
path. Comparison of physical regulated bills, INTEGRABLE numerator & nonzero
denominator, no reweighting in this limit. -/
theorem chartWithBareLaw (s : ℕ) (S : Finset Cover) {F : P.Test}
    (p : InTest (Kc) true S false F.val) (n : CovCover (Kc) F.val) :
    ∃ A : (u : ℕ) → Evaluation (side P.run (iPath P u) (depth P u)),
    (∀ᶠ u in atTop,
      W P (iPath P u) (kPath P u) 1 ≠ 0 ∧
      let R := More (side P.run (iPath P u) (depth P u));
      covariant (toMark (A u)) ∧
      AtSupport false (Satin.region ((followBox («Λ»:=P.par) (l:=P.width))^[depth P u-s] S) _) (toMark (A u)) ∧
      Integrable (bareWeight P (iPath P u) (kPath P u) (bareBeta P (depth P u)) (A u)) (prior SU.group R) ∧
      Journey.compass (Y) (iPath P u) (kPath P u) s (exhibit (Y) P.large s (iPath P u) F.val) =
        W P (iPath P u) (kPath P u) (A u) / W P (iPath P u) (kPath P u) 1) ∧
    Tendsto (fun u=> W P (iPath P u) (kPath P u) (A u) / W P (iPath P u) (kPath P u) 1) atTop (𝓝 (P.E s F.val)) := by
  let E(u:ℕ) : Mark (side P.run (iPath P u) s):= exhibit (Y) P.large s (iPath P u) F.val
  have hpos (u : ℕ): AtSupport false (Satin.region S _) (E u):= Tapestry.exhibited (Y) P.large _ _ _ p
  have hg (u:ℕ): covariant (E u) := Tapestry.validate (Y) P.large _ _ n
  let pays (u:ℕ):= Tapestry.Pay (Y) s (iPath P u) (kPath P u)
  have hau(u:ℕ) : ∃ M : Mark (side P.run (iPath P u) (depth P u)),
     pays u → covariant M ∧
      AtSupport false (Satin.region ((followBox («Λ»:=P.par) (l:=P.width))^[depth P u-s] S) _) M ∧
      Journey.compass (Y) (iPath P u) (kPath P u) s (E u) =
      Journey.compass (Y) (iPath P u) (kPath P u) (depth P u) M := by
    by_cases h: pays u
    swap; · exact ⟨0,fun a=>(h a).elim⟩
    obtain ⟨M,hC,hA,he⟩:=compassAsc P (iPath P u) (kPath P u) s (depth P u) h.2 ⟨h.1,le_rfl⟩ (E u) S (hpos u)
    exact ⟨M,fun _=>⟨hA (hg u),hC,he⟩⟩
  choose M hM using hau
  let A(u:ℕ):= diagMark (M u)
  have hW(u:ℕ)(h:pays u) : W P (iPath P u) (kPath P u) 1 ≠ 0 ∧
      Journey.compass (Y) (iPath P u) (kPath P u) s (E u) = W P (iPath P u) (kPath P u) (A u)/W P (iPath P u) (kPath P u) 1 := by
    obtain ⟨hz,hc⟩:= compassWpath P u (hM u h).2.1.env h.1
    exact ⟨hz,(hM u h).2.2.trans hc⟩
  have hpays:∀ᶠ u in atTop,pays u:= (P.history.finance s).mono (fun _ h=> ⟨h.depth,h.enters⟩)
  refine ⟨A,?_,(chart P s S p).congr' (hpays.mono (fun u v=> (hW u v).2))⟩
  filter_upwards [hpays] with u h
  exact ⟨(hW u h).1,Reconstruction.diag_cov (hM u h).1,
     Reconstruction.diagAt (hM u h).2.1,
     bare_integrable P _ _ h.1 _ _ (Env.along (hM u h).2.1.env (measurable_id.prodMk measurable_id)),(hW u h).2⟩
open SectorNext.Remainder.Scales
open Papal
-- L.2 exact exponent, *all i and k* (kicked and s≤cutoff), not a
-- ⋯limit i alone. Native units (sites counts More N). Using the newer
-- project's Meritorious Hallway qualification on this course, not needing to
-- re-prove the intermediate WheelExact etc procurement on the older source.
private lemma merit_scale (L : Side) (x : ℝ) (h : 0 < x) : merit L x ≤ x^(-(1/4:ℝ)) := by
  have hL : 1 ≤ (L.val:ℝ) := by exact_mod_cast L.property
  let a := Pressure.betaF SU.group x L
  have ha : x ≤ a := le_add_of_nonneg_right (mul_nonneg (Gauge.slopeConstant_pos Thera.yet_one).le (Real.log_nonneg hL))
  have hb:0 ≤ a:= (h.trans_le ha).le
  unfold merit g SectorNext.Remainder.Scales.y Next.Scheduling.Clock.gap
  change Real.sqrt (Real.sqrt a)⁻¹ ≤ _
  simp_rw [Real.sqrt_eq_rpow, ←Real.rpow_neg hb, ← Real.rpow_mul hb]
  refine le_trans ?_ (Real.rpow_le_rpow_of_nonpos h ha (z:=-(1/4:ℝ)) (by norm_num)); exact le_of_eq (congr_arg _ (by ring))

lemma Ldenominator (h : Meritorious P.par) (a : ℝ) (p : 0<a) :
    ∀ᶠ s in atTop,∀ i k :ℕ, Pay (Y) s i k → let X := hat (Λ).R.L (Λ).x s
      Real.exp (sod (Y) k s i - (a* X^(-(1/4:ℝ))) * sites (side P.run i s)) ≤
      ‖Complex.exp (- (gramAt P i k s).v) * partitionZ (gramAt P i k s) (Λ).U (((Y).voyage i).CapeT s)‖ := by
  filter_upwards [line_merit (Y) a p h, (turnover (Λ)).eventually_gt_atTop 0] with s t hX i k hp
  exact (t _ _ hp.1 hp.2).trans' (Real.exp_le_exp.mpr
    (sub_le_sub_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (merit_scale _ _ hX) p.le)
        (zero_le_one.trans (sites_pos _))) _))

/-- Also at top with the common-bare denominator on the *same* path. -/
lemma topNotTooCancelled (h : Meritorious P.par) (a : ℝ) (p : 0<a) :
    ∀ᶠ u in atTop, let i:=iPath P u; let k:=kPath P u; let s:=depth P u; let X:=hat (Λ).R.L (Λ).x s
      Real.exp ((sod (Y) k s i - (a* X^(-(1/4:ℝ)))*sites (side P.run i s))+(gramAt P i k s).v.re) ≤
      ‖W P i k 1‖ := by
  filter_upwards [(path_limits P).1.eventually (Ldenominator P h a p), P.history.finance 0] with u hx hk
  let s:=depth P u; let l:=iPath P u; let j:=kPath P u
  let z:=gramAt P l j s; let W0:=W P l j 1
  let b:=sod (Y) j s l - (a* (hat (Λ).R.L (Λ).x s)^(-(1/4:ℝ)))*sites (side P.run l s)
  have ht : Real.exp b ≤ ‖Complex.exp (-z.v)*W0‖ := by
    apply (hx l j ⟨hk.depth,le_rfl⟩).trans
    apply le_of_eq; congr 2
    show partitionZ (gramAt P l j ((Y).uv j)) (Λ).U (((Y).voyage l).CapeT ((Y).uv j)) = W0
    rw [partitionW P l j hk.depth]
    change W P l j (fun U=> tilt P l j (eff P l j s) (bareBeta P (depth P u)) U • 1)=W P l j 1
    rw [beta_match P u]; unfold s l j tilt; simp; rfl
  change Real.exp (b+z.v.re) ≤ ‖W0‖
  rw [norm_mul,Complex.norm_exp, Complex.neg_re, Real.exp_neg, inv_mul_eq_div] at ht
  rw [Real.exp_add]; exact (le_div_iff₀ (Real.exp_pos _)).mp ht
end PureForce
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

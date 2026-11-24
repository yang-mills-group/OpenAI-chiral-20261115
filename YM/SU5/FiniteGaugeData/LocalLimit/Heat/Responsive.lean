import YM.SU5.FiniteGaugeData.LocalLimit.Heat.GaugeObservable
import YM.SU5.FiniteGaugeData.LocalLimit.Heat.WaveObservable

/-!
# Responsiveness of the Vp929 canonical step

The upper steps need not give arrays holomorphic in the guesses, so establish
individual-step continuity of physical parameters assuming **density** continuity
through the offshell stove. Only the lower steps are meant to have been issued by
this Service. Such continuity is of fixed-volume use (to elect the donors).
-/
set_option autoImplicit false
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
namespace LocalLimit

private lemma picks_continuously {T E : Type*} [TopologicalSpace T] [PseudoMetricSpace E]
    (S : Set E) (p : T → E) (f : T → E → E) (hp : ∀ t, p t ∈ S) (H : ∀ t, f t (p t) = p t)
    (hf : ∀ t y z, y∈ S → z∈ S → dist (f t y) (f t z) ≤ dist y z / 2)
    (hc : ∀ t, ContinuousAt (fun u=> f u (p t)) t) : Continuous p := by
  refine continuous_iff_continuousAt.mpr fun x=> Metric.continuousAt_iff'.mpr fun ε h=>?_
  filter_upwards [Metric.continuousAt_iff'.mp (hc x) (ε/2) (half_pos h)] with t ht
  change dist (f t (p x)) (f x (p x)) < _ at ht; rw [H] at ht
  have he := hf t _ _ (hp t) (hp x)
  rw [H] at he
  linarith only [he,ht,dist_triangle (p t) (f t (p x)) (p x)]
set_option quotPrecheck false

variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
variable {d : ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
    {h x r D D' : ℝ} {p p' : BudgetPoint} {w : Location (R:=R) B m n}
local notation "Ω" => mid m B
local notation "Π" => mid n B
local notation "μw" => Pair ↥SpaceM
open Pitching Focus

/-- Continuity for the off-shell Wear output in a history comparing to CapP.
Modeled here just as the test we need the input family to meet. -/
def stoveTest (J : Robes N V W) (q : Chi) (w : Location (R:=R) B m n) (p p' : BudgetPoint)
    {T : Type*} [TopologicalSpace T] (A : T → Corr (mid n B)) (β : T → ℝ) (v : T → ℂ) : Prop :=
  ∀ f : T → SpaceM, Continuous f → ∀ r:ℝ,(∀ t,‖f t‖ ≤ r) →
    ∀ y : Orbit Ω, Rue.FleetS p.threshold y.1 → Continuous fun t=>
      stove U w.coarse (w.buildIn V p' (β t) (A t) (v t)) w.fine w.G (w.step V) q J.d (f t).val y

/-- Supplemental real-path grant of the canonical rate prescription.
Preserve continuity of posted beta and of wave (not of offset). -/
def Responsive (J : Robes N V W) (q : Chi) (w : Location (R:=R) B m n) (h x : ℝ)
    (p p' : BudgetPoint) (s : Operation Ω Π) : Prop :=
  ∀ (T : Type) [TopologicalSpace T] (A : T → Corr Π) (β : T → ℝ) (v : T → ℂ),
      Continuous β → (∀ t, enters (x+billX R.L) (β t)) →
      (∀ t, Charged p' w.input K.j R.L.val h (3*dleaf R.L x) (A t)) →
      stoveTest J q w p p' A β v →
      Continuous (fun t=> s.posted (β t) (A t)) ∧ Continuous fun t=> s.wave (β t) (A t)

section shop

variable [Nonempty (Haro.ΘS r)] (s : Shop w J p p' q h x r)
variable {T : Type*} [TopologicalSpace T] (A : T → Corr (mid n B)) (β : T → ℝ) (v : T → ℂ)
    (hβ : Continuous β) {N0 : ℕ} (hx : Location.Request V U W J q w N0 x p p')
    (hc : ∀ t, Client K R x w.input p' h (β t) (A t,0))
    (ht : stoveTest J q w p p' A β v)

local notation "𝔹" => closedBall (0:μw) (r/2)
include hx hc ht
open Test TestW Sour.MatchW Sour.MatchW.Technique

private lemma real_response (u:μw) (hp:u∈𝔹) (g:u.2=0) :
    Continuous fun t=> s.multiplier (β t) (A t,0) u := by
  let E(t) := (s.stepV (β t) (A t,0) u).1
  choose Δ o F HF using (fun t=> (s.emits (hc t) u hp g (v t)).2.2)
  let Gt(t) := (E t,F t)
  let Wt(t) := (β t + w.movement V - Δ t)
  let tags : Ids Ω := Classical.arbitrary _
  let Y : Orbit Ω := (1,tags)
  have he t :
      denZ (w.buildOut V p (Wt t) (Gt t) (o t)) U w.coarse Y =
      stove U w.coarse (w.buildIn V p' (β t) (A t) (v t)) w.fine w.G (w.step V) q J.d u.1.val Y :=
    (HF t).wear Y (clear_identity p)
  let ψ := ht (fun _=> u.1) continuous_const ‖u.1‖ (fun _=> le_rfl) Y (clear_identity p)
  let hp' := hx.rocket.paid
  let pR : Roof Ω J.k d J.n w.coarse := { hp' with paid := fun x => (hp'.paid x).shrink J.hr.le }
  have hv : Continuous fun t=> waveTest w.freq (E t) K.j w.output.M :=
    continuous_wave_of_dens hx.boot.power s.A0.dream.floor s.s.k s.GraspY pR (J.gran.trans hx.rocket.size) hx.pole
      Gt (fun _=> houseP p K s.Aχ s.Γχ s.Λf) Wt o tags (ψ.congr fun i=> (he i).symm)
      (fun i=> (s.emits (hc i) u hp g (v i)).2.1)
  exact (show Continuous fun t=> (u.1 + waveTest w.freq (E t) K.j w.output.M,(0:SpaceM))
    from (continuous_const.add hv).prodMk continuous_const).congr (fun t=> Prod.ext rfl (s.real_aim (hc t) u hp g).symm)

private lemma real_fixed_continuous : Continuous fun t=> s.pickW (β t) (A t,0) := by
  let f(t:T) := s.multiplier (β t) (A t,0)
  refine picks_continuously 𝔹 _ f (fun t=> (s.sleepsW (hc t)).1.1) (fun t=> (s.sleepsW (hc t)).1.2) ?_ ?_
  · intro t a b ha hb; refine ((s.march_Point (hc t)).2.dist_le_mul _ ha _ hb).trans_eq ?_; push_cast; ring
  exact fun t => (real_response s A β v hx hc ht _ (s.sleepsW (hc t)).1.1 (s.real_pick (hc t))).continuousAt
omit ht hc

lemma realStep_receipt (H : Shop.Ready D D' s) (hu : Capsule R x) : Responsive J q w h x p p' s.operate := by
  intro T t A β v hs ht he hv
  have h(t:T) := s.worn (s:=hu) H
  let X(t) := s.operate.output V w p (β t) (A t) (v t)
  let Q(t) := s.operate.wave (β t) (A t)
  have hw : Continuous Q := continuous_fst.comp (real_fixed_continuous s A β v hx
    (fun t=> submits hu (ht t) ⟨he t, Charged.zero.mono (mul_nonneg (by norm_num) hu.high.le)⟩) hv)
  let E(t) := (h t).real (β t) (A t) (v t) (ht t) (he t)
  let tags : Ids Ω := Classical.arbitrary _
  let hp' := hx.rocket.paid
  have hB : Continuous fun t=> (X t).beta := continuous_beta_of_dens s.A0.dream.floor { hp' with paid:=fun i=>(hp'.paid i).shrink J.hr.le } (J.gran.trans hx.rocket.size) s.GraspY (V.L.mood (w.lag+1)) tags
      (fun t=> s.operate.realArr (β t) (A t)) (fun t=> (X t).v) (fun t=> (X t).beta)
      (fun t=> ((h t).cost _ _ (ht t) ⟨he t,Charged.zero.mono (mul_nonneg (by norm_num) hu.high.le)⟩).1.1.inc)
      (fun t=> (E t).2.2.2.1.1) (fun y c=> (hv Q hw r (fun t=> (E t).2.2.1) (y,tags) c).congr fun t=>( (E t).2.2.2.2.1 (y,tags) c).symm)
  exact ⟨((hs.add (continuous_const (y:=w.movement V))).sub hB).congr fun t=> sub_sub_cancel _ _,hw⟩
end shop

/-- Additional grant of the pre-pivot election. -/
def ResponsiveService (J : Robes N V W) (q : Chi) (N0 : ℕ) (h d : ℝ) (P : Prescription R B) : Prop :=
  ∀ (m n) (u : Location (R:=R) B m n) x p p', d ≤ x → Location.Request V U W J q u N0 x p p' →
    Responsive J q u h x p p' (P m n u x p p')

variable {R0 δ C: ℝ→ℝ} {N0:ℕ}
-- `Vp929/Stage/Plant.supplyΛ`, strengthened to record Responsive instead
-- of discarding the real-path data when existentially quantifying the step map.
theorem supplyResponsive (F:∀ᶠ x in atTop,Funded (R0 x) (δ x) (C x) x N0 J q h)
    (t:Chill_v δ)(hc:∀ᶠ x in atTop, 0 ≤ δ x) :
    ∃ (P:Prescription R B)(d:ℝ), Service V U W J q h δ C R0 P N0 d ∧
      ResponsiveService J q N0 h d P := by
  have nonemp (t:ℝ)(h:0 ≤ t) : Nonempty (Haro.ΘS t) := ⟨⟨0,(norm_zero |>.trans_le h)⟩⟩
  obtain ⟨d,qT⟩:= eventually_atTop.mp (F.and (prolong (V:=V) t hc))
  have ξ (m n:Side)(w:Location (R:=R) B m n)(x:ℝ)(p p':BudgetPoint):
      ∃ P : Operation (mid m B) (mid n B),∀ [Nonempty (Haro.ΘS (R0 x))], d ≤ x →
      Location.Request V U W J q w N0 x p p' → ∃ S:Shop w J p p' q h x (R0 x),Shop.Ready (δ x) (C x) S ∧ P=S.operate:=by
    by_cases z:d ≤ x ∧ Location.Request V U W J q w N0 x p p'; swap
    · exact ⟨⟨0,0,0,0⟩,fun t v=>False.elim (z ⟨t,v⟩)⟩
    letI:=nonemp (R0 x) (qT x z.1).1.hi.le; obtain ⟨S,T⟩:= (qT x z.1).1.ready _ _ w p p' z.2; exact ⟨S.operate,fun _ _=> ⟨S,T,rfl⟩⟩
  choose P hP using ξ
  refine ⟨P,d, ⟨fun m n w x p p' y hz=> ?_,?_⟩,?_⟩
  · letI:=nonemp _ (qT x y).1.hi.le; obtain ⟨T,w',v⟩:= hP m n w x p p' y hz; rw [v]; exact T.worn (s:=(qT x y).2) w'
  · intro m n w x x' p p' P₀ P₁ y y' hw hz b E E' v v' q1 q2 e1 e2 L L' Z Z' pΨ
    let k:= (qT x y); let k':=(qT x' y'); letI:=nonemp _ k.1.hi.le; letI:=nonemp _ k'.1.hi.le
    obtain ⟨l,u,note⟩:=hP _ _ w _ _ _ y hw; obtain ⟨l',v',note'⟩:=hP _ _ w _ _ _ y' hz; unfold Z Z' L L'; rw [note,note']
    exact l.prosper l' (submits k.2 q1 ⟨e1,Charged.zero.mono (show 0 ≤ 3* dleaf R.L x from mul_nonneg (by norm_num) k.2.high.le)⟩) (submits k'.2 q2 ⟨e2,Charged.zero.mono (show 0 ≤ 3*dleaf R.L x' from mul_nonneg (by norm_num) k'.2.high.le)⟩) pΨ hw hz
  intro m n w x p p' y hz
  letI := nonemp _ (qT x y).1.hi.le
  obtain ⟨s,r,hs⟩ := hP m n w x p p' y hz
  rw [hs]
  exact realStep_receipt s hz r (qT x y).2

end LocalLimit
end YM.CF.Py.Rate

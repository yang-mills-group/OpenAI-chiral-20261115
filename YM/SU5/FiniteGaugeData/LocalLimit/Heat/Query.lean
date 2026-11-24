import YM.SU5.FiniteGaugeData.LocalLimit.Heat.Responsive
import YM.SU5.FiniteGaugeData.LocalLimit.Heat.ContinuousStove
import YM.CF.Vp929.Budget.Read
import YM.CF.Vp929.Stage.Spine

/-!
# Off-shell canonical queries

One lower step of the mixed election in the temperature box.
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

variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
    {d e δ D C b x r σ u : ℝ} {m n B N : Side}
    {U : Grasp V.U B d} {W : GivenX V U} {p p' : BudgetPoint} {T : Type} [TopologicalSpace T]
    {J : Robes N V W} {q : Chi}
local notation "Ω" => mid m B
local notation "Ω'" => mid n B
open Push.BetaTransport

private lemma reprice {A : PathData SU.group} {F : Corr (mid m B)} {S : Scree.Loom (mid m B)} {I : Interest (mid m B)}
    {f : Clip} (b' b : ℝ) (v : ℂ) (u : Orbit Ω) : denZ (construct p A f I b' F v) U S u =
    Complex.exp (((b-b') * kinetic A f p u.1 : ℝ):ℂ) • denZ (construct p A f I b F v) U S u := by
  unfold denZ
  rw [smul_smul,←Complex.exp_add]
  congr 2
  unfold GramM.betaL GramM.H0
  dsimp only [construct]
  rw [channels_split u.1 b, channels_split u.1 b']; push_cast; ring

lemma continuous_dens_raw
    {A : PathData SU.group} {F : T → Corr (mid m B)} {S : Scree.Loom (mid m B)}
    {I : Interest (mid m B)} {f : Clip} (u : Orbit Ω) {β : T → ℝ} {v : T → ℂ}
    (hv : Continuous v) (hβ : Continuous β) (hF : Beau.LampF (fun t=> (F t).1))
    (ht : ∀ i:Scree.Force Ω, ∀ y, Continuous fun t=> (F t).2 i y) :
    Continuous fun t=> denZ (construct p A f I (β t) (F t) (v t)) U S u := by
  let Z(t:T) := construct p A f I (β t) (F t) (v t)
  let Y := relV U I (S u)
  let P := (tale_L Y).comp (tankL (spar K.j I.M (S u)))
  change Continuous fun t=> Complex.exp ((Z t).betaL S u) • P ((Z t).board u)
  refine Continuous.smul (f:=fun t=> Complex.exp ((Z t).betaL S u)) (g:=fun t=> P ((Z t).board u)) ?_ ?_
  · refine Complex.continuous_exp.comp (f:=fun t=> (Z t).betaL S u) ?_
    change Continuous fun t=> v t - (A.inChannels f p (β t) u.1:ℝ) - Pec.pigment I.I (S u)
    simp_rw [channels_split u.1 (β _)]; exact (hv.sub (Complex.continuous_ofReal.comp ((hβ.mul continuous_const).add continuous_const))).sub continuous_const
  refine P.continuous.comp (f:=fun t=> (Z t).board u) ?_
  dsimp only [Z,construct,GramM.board]; simp_rw [Vale.still_Footprint,add_zero]
  letI : NormedAlgebra ℚ (Cipher Ω) := NormedAlgebra.restrictScalars ℚ ℝ (Cipher Ω)
  exact (exp_continuous.comp (Fixed.Voltage.lamp_rank p (fun t=> (F t).1) u.1 hF)).mul
    (Fixed.Voltage.lamp_fuel p (fun t=> (F t).2) ht u)

section generic
variable {I : Interest (mid m B)} {S : Scree.Loom (mid m B)} {k l : ℕ}
-- Recover absolute bound on the actual *unnormalized* ket for same-period dominated integrals.
omit [TopologicalSpace T] in
lemma capped_exp (hw : InterestX W.C _ I) (hf : Roof (mid m B) u d k S) (ht : U.roundZ ≤ (mid m B).val)
    (a : T → ℝ) (v : T → ℂ) (A : T → Corr (mid m B)) (hs : 1 ≤ r)
    (he : ∀ i, 0 ≤ a i ∧ a i ≤ x) (hv : ∃ c:ℝ,∀ i,(v i).re ≤ c)
    (hl : ∀ i, Cost p r δ (A i)) :
    ∃ C:ℝ,∀ i y, ‖denZ (construct p (V.L.path l) K.top.clip I (a i) (A i) (v i)) U S y‖ ≤ C := by
  let Z(i:T) := construct p (V.L.path l) K.top.clip I (a i) (A i) (v i)
  let L := Real.exp (earnings W p x δ * sites Ω)
  obtain ⟨c,hc⟩ := hv
  refine ⟨Real.exp c * L, fun i y => ?_⟩
  have h : (Real.exp (v i).re)⁻¹ * ‖denZ (Z i) U S y‖ ≤ L := by
    rw [←Real.exp_neg,←Complex.neg_re,←Complex.norm_exp,←norm_smul]; exact extensive W hw hf l ht hs _ _ ((hl _).lot _ _) (he _).1 (he _).2 _
  change ‖denZ (Z i) U S y‖ ≤ _
  exact ((inv_mul_le_iff₀ (Real.exp_pos _)).mp h).trans (mul_le_mul_of_nonneg_right (Real.exp_monotone (hc i)) (Real.exp_pos _).le)
end generic

/-!
Pack the three parts of the receipt needed for continuity after further steps.
Pass back the *queried* beta (not asserting Wear at that guess until after
solving) and accumulate the bound on offsets separately.
-/
structure Cleared
    (W : GivenX V U) (h a : ℝ) (p : BudgetPoint) (I : Interest Ω) (l : ℕ)
    (F : Scree.Loom Ω) (A : T → Corr Ω) (β : T → ℝ) (v : T → ℂ) : Prop where
  cont (y : Orbit Ω) : Rue.FleetS p.threshold y.1 → Continuous fun t=>
    denZ (construct p (V.L.path l) K.top.clip I (β t) (A t) (v t)) U F y
  cost (t : T) : Charged p I K.j R.L.val h a (A t)
  offset : ∃ c:ℝ,∀ i,(v i).re≤c

lemma Cleared.up {h a a':ℝ} {I : Interest (mid m B)} {l : ℕ} {F : Scree.Loom (mid m B)}
    {A : T → Corr (mid m B)} {β : T → ℝ} {v : T → ℂ} (p : BudgetPoint) (e:a ≤ a')
    (cp : Cleared W h a p I l F A β v) : Cleared W h a' p I l F A β v :=
  ⟨cp.cont,fun t=> (cp.cost t).mono e,cp.offset⟩

variable [FirstCountableTopology T] {x : ℝ} {h R0 Δ b₀ : ℝ} {N0 : ℕ}
    {w : Location (R:=R) B m n}
    {P : Prescription R B} {D C Q : ℝ→ℝ}

private lemma enroll_axes {a : ℝ} (h : 0 ≤ x) (H : enters x a) : 0 ≤ a ∧ a ≤ 2*x := by
  have h₁ : 53/100*x ≤ a := H.1
  have h₂ : a ≤ 7/4*x := H.2.1
  constructor <;> linarith

private lemma as_request {X : ℝ} (e : 0≤ X) {a : ℝ} (g : enters X a) : matchedX X a := by
  have he : 53/100*X ≤ a := g.1
  exact ⟨by linarith, (enroll_axes e g).2⟩

local notation "Yt" => x+billX R.L
variable {Z : Operation (mid m B) (mid n B)} {A : T→ Corr (mid n B)} {β β' : T→ℝ} {v:T→ℂ} (hh : 1≤ h)
    (hx : Prices R.L D x)
    (hb : Location.Request V U W J q w N0 x p p') (H : Certified V U W J q h x p p' (Q x) (D x) (C x) w Z)
    (qP : Responsive J q w h x p p' Z)
    (hu : Cleared W h (dleaf R.L (x+billX R.L)) p' w.input w.lag w.fine A β' v)
    (hβ : Continuous β') (hf : ∀ t, enters (x+billX R.L) (β' t))
local notation "ψ" k => Z.realArr (β' k) (A k)
local notation "Φ" k => Z.posted (β' k) (A k)
local notation "pβ" k => Z.wave (β' k) (A k)
local notation "νp" k => Z.offset (β' k) (A k) (v k)
local notation "vol" => sites Ω
include hh hx H hu hb qP hβ hf


lemma step_query (e : Continuous β) :
    (Continuous fun t=> Z.posted (β' t) (A t)) ∧ (Continuous fun t=> Z.wave (β' t) (A t)) ∧
    (∀ t, |Φ t| ≤ D x ∧ ‖pβ t‖ ≤ Q x ∧ |(νp t).re - (v t).re| ≤ C x * sites (mid m B) ∧
      ∀ y, Rue.FleetS p.threshold y.1 → denZ (w.buildOut V p (β' t + w.movement V - Φ t) (ψ t) (νp t)) U w.coarse y =
            stove U w.coarse (w.buildIn V p' (β' t) (A t) (v t)) w.fine w.G (w.step V) q J.d (pβ t).val y) ∧
    Cleared W h (dleaf R.L x / 1000) p w.output (w.lag+1) w.coarse
       (fun t=>Z.realArr (β' t) (A t)) β (fun t=>Z.offset (β' t) (A t) (v t)) := by
  -- hf on input; no assumption on coarse guess β
  let δz := 3*dleaf R.L x
  let S := w.step V
  let I(t) := w.buildIn V p' (β' t) (A t) (v t)
  have he := hu.up p' (le_trans (hx.leaf_mono _ (le_add_of_nonneg_right hx.slope.le)) (by dsimp only [δz]; linarith [hx.leaf] : dleaf R.L x ≤ δz))
  have hX : 0 ≤ Yt := by linarith [hx.grade,hx.slope]
  have hA : S.patch.Branches S.kernel SU.group := by unfold S Location.step; rw [V.L.patch_x]; exact V.L.cloth
  have hu'(t:T) : Nonempty (Girt.BaseL U w.G (I t) w.coarse w.fine q J.d) := by
    let pT:= hb.statv (β' t) (A t) 0 (v t) (as_request hX (hf t)); exact rig V U W J q hb.rocket _ hb.roof _ pT.sound w.count (ward_m (V.L.mood w.lag) ((he.cost t).toCost.lot _ _))
  have pS : stoveTest J q w p p' A β' v := by
    intro f g r hr y _
    cases isEmpty_or_nonempty T
    · exact continuous_iff_continuousAt.mpr fun t=> isEmptyElim t
    let a₀ := Classical.arbitrary T
    let pT := hb.statv (β' a₀) (A a₀) 0 (v a₀) (as_request hX (hf a₀))
    have gT : InterestX W.C _ w.input := pT.sound
    have he' := hb.roof
    obtain ⟨c,Hc⟩ := capped_exp (l:=w.lag) gT { he' with paid:=fun i=>(he'.paid i).shrink J.hr.le } (J.gran.trans hb.fineSize)
      β' v A hh (fun i=>enroll_axes hX (hf i)) he.offset (fun i=> (he.cost i).toCost)
    refine continuous_stove (b:=2*(Yt)) _ w.coarse w.fine S pT.hunt.scaleP hA I f hu' Hc
      ((ae_fleet hb.isle').mono fun y v=> hu.cont y v) hβ g (fun i=>?_) hr y
    rw [show (I i).beta = β' i from rfl]; rw [abs_of_nonneg (enroll_axes hX (hf _)).1]
    exact (enroll_axes hX (hf _)).2
  obtain ⟨cp,cz⟩ := qP T A β' v hβ hf he.cost pS
  let vM(t) := νp t
  let Xb(t:T) := β' t + w.movement V - Φ t
  have hz : Continuous Xb := (hβ.add continuous_const).sub cp
  have hp t := H.real (β' t) (A t) (v t) (hf t) (he.cost t)
  have ha t := H.cost _ (A t,0) (hf t) ⟨he.cost t,Charged.zero.mono (show 0 ≤ 3*dleaf R.L x from mul_nonneg (by norm_num) hx.leaf.le)⟩
  refine ⟨cp,cz,fun t=>⟨(Complex.abs_re_le_norm _).trans (ha t).2,(hp t).2.2.1,(hp t).2.2.2.2.2,(hp t).2.2.2.2.1⟩,⟨?_, fun t=> (ha t).1.1,?_⟩⟩
  · intro i t
    have g := (pS (fun t=> pβ t) cz _ (fun t=> (hp t).2.2.1) i t).congr fun y=> ((hp y).2.2.2.2.1 i t).symm
    refine Continuous.congr (g:=fun t=>denZ (w.buildOut V p (β t) (ψ t) (vM t)) U w.coarse i)
        ((Complex.continuous_exp.comp (Complex.continuous_ofReal.comp ((hz.sub e).mul (continuous_const (y:=kinetic (V.L.path (w.lag+1)) K.top.clip p i.1))))).smul g) fun j=>
      (reprice (V:=V) (β j) (Xb j) (vM j) i).symm
  obtain ⟨c,h⟩ := hu.offset
  exact ⟨c + C x*vol, fun t=> by linarith only [h t,(abs_le.mp (hp t).2.2.2.2.2).2]⟩

end LocalLimit
end YM.CF.Py.Rate

import YM.SU5.FiniteGaugeData.LocalLimit.Transfer.Downstairs
import YM.SU5.FiniteGaugeData.LocalLimit.Transfer.Cone

/-!
# Horizontal transfer (one period)

Actual estimates, pointwise. The large-m extension of the horizontal estimate
(including outside cone) can have catastrophically large RHS. Pairs must already be
elected as in the bridge (which uses period-dependent eventual cutoff thresholds).
-/
set_option autoImplicit false
set_option quotPrecheck false
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
open Chaff Gloss Maize Tye RP RP.Str Oise
namespace LocalLimit

open Branch
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
    {d : ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
    {h x delay wα y : ℝ} {C D Q R0 E Cf δ Fp : ℝ→ℝ} {P : Prescription R B} {W0 : Cape m B R.L}
    {n b N0 : ℕ} {T : Month x 1 6 2 N0 V W} {f B0 : ℕ → ℝ} (ht : T.q ≤ m.val)
    {D' : Heron V 1 2 6 N0 0 J q h wα R0 E Cf δ y} {hy : y ≤ x} {V0 Jx : ℕ → ℝ}
local notation "Ω" => cell m B R.L
local notation "kT" => trunkY n b
local notation "kS" => buoy n
local notation "B'" => ActualSpine T ht W0 f kT
local notation "BT" => Actual T ht W0 f kT
local notation "Yb" i:max => dleaf R.L (hat R.L x i)
local notation "Γ" => StarPS kT
local notation "Φ" i:max => wage_B n b i R.L x


open Graph.Diff Graph.Angle Window

-- Census *per gauge site*
def jumpCost (_V : Grace K R L) (p : BudgetPoint) : ℝ := let F:=K.top.clip; let C:=K.top.paths; let a:=p.threshold;
  6 * (F.direct*2+F.linear*a*2+(C*2)^2/2) + (C*a^3+C*a^4)

private lemma jump_account (s : Side) (p : BudgetPoint) :
    jumpTax p (More s) K.top.clip K.top.paths = jumpCost V p * sites s := by
  have he : Fintype.card (Face (Per (More s)))= (More s).val^4 * 6 := by
    change Fintype.card (Site (More s) × PlaqAxes) = _; rw [Fintype.card_prod, site_card, show Fintype.card PlaqAxes=6 from by decide]
  unfold jumpCost jumpTax pivotTax sites; rw [he]; dsimp only; push_cast; ring

section trace
variable {F : BudgetPoint} {I : Interest (mid m B)} {A B'c : Corr (mid m B)} {l : ℕ}
    {LQ : Scree.Loom (mid m B)} {c₁ c₂ : ℂ} {δz z₁ z₂ a d₁ b' u : ℝ}
local notation "πF" => construct F (V.L.path l) K.top.clip I
local notation "Cn" => K.top.paths
local notation "ΦA" => πF z₁ A c₁
local notation "ΦB" => πF z₂ B'c c₂
local notation "Λ" => mid m B
local notation "EC" => earnings W F a δz
local notation "Ψ" => Record.paceZ F (mid m B) K.top.clip K.top.paths d₁ b'

private lemma measure_law 
    (T' : Orbit (mid m B)) (hβ : 0≤z₂) (he : z₂≤a) : Graph.past ΦB T'.1 * Real.exp (flagBill (mid m B) δz δz (cashU W.C)) ≤ Real.exp (EC*sites (mid m B)) := by
  let hv:=V.L.mood l
  have hp : - (V.L.path l).inChannels K.top.clip F z₂ T'.1 ≤ taxPart V F a * sites (mid m B) := by
    have ht := Window.energy_low F (V.L.path l) K.top.clip hv hβ T'.1; exact ((neg_le.mp ht).trans (tax_price V (mid m B) he)) -- tune
  rw [Graph.past,←Real.exp_add]; apply Real.exp_monotone
  change -(V.L.path l).inChannels _ _ _ _+_≤ _
  refine (add_le_add_left hp _).trans_eq ?_; rw [flagBill_eq]; unfold earnings sites; change _+_= _ * ((((mid m B).val*2:ℕ):ℝ)^4); push_cast; ring

private lemma transfer_record {k : ℕ} (hA : Cost F h δz A) (hB : Cost F h δz B'c)
    (p : Cost F h b' (A-B'c)) (δP : |z₁-z₂| ≤ d₁) (hh:1≤h) (hq:0 ≤ δz) (hp:0 ≤ b')
    (hw : InterestX W.C (mid m B) I) (H : Roof (mid m B) u d k LQ) (hc : U.roundZ ≤ (mid m B).val)
    (hx : 0≤z₁)(hy : 0≤z₂)(h1 : z₁≤a)(h2 : z₂≤a)(T' : Orbit (mid m B)) :
    ‖field U ΦA LQ T' - field U ΦB LQ T'‖ ≤ 2 * Ψ * Real.exp (EC * sites (mid m B)) := by
  have hg:= V.L.mood l; let v:= levelQ W.C; let w:= cashU W.C
  have pT := paths_nonneg V
  let g:= d₁ * jumpTax F (More Λ) K.top.clip Cn; let f:= Graph.Diff.rankV Λ b'
  have hf: 0 ≤ f := by unfold f Graph.Diff.rankV; positivity
  have hG : 0 ≤ g := mul_nonneg ((abs_nonneg _).trans δP)
    ((abs_nonneg _).trans (kinetic_P (T'.1) hg pT))
  let x := Record.paceZ F (mid m B) K.top.clip K.top.paths d₁ b'; let s:= Real.exp (EC* sites (mid m B)); have he: 0<s:=Real.exp_pos _
  have hz : x=2*g+3*f := rfl; have hx0 : 0≤x:=by linarith
  by_cases u:g≤1/2 ∧ f≤1/2; swap
  · have hwx : 1 ≤ x := by push Not at u; by_cases h':g≤1/2; linarith [u h']; linarith
    calc
      _ ≤ s+s := (norm_sub_le ..).trans (add_le_add (extensive W hw H l hc hh _ _ (hA.lot _ _) hx h1 _) (extensive W hw H l hc hh _ _ (hB.lot _ _) hy h2 _))
      _ ≤ _ := by change s+s ≤ 2*x*s; nlinarith
  have p0 := frostQ (X:=ΦA) (hA.lot _ _) (zero_le_one.trans hh) hw
  have p1 := frostQ (X:=ΦB) (hB.lot _ _) (zero_le_one.trans hh) hw
  let Uc:Record.Cart ΦA ΦB h Cn b' d₁ := ⟨rfl,rfl,rfl,rfl,δP,rfl,rfl, ⟨⟨p.inc.weight,fun _ v=> v.elim⟩,⟨p.dark.weight,fun _ v=> v.elim⟩⟩,u.1,u.2⟩
  refine (Record.on_trace ΦA ΦB LQ H hc Uc hg p0 p1 hh hq (cash_v _) (level_p _).le pT T').trans ?_
  refine (mul_le_mul_of_nonneg_right (measure_law (I:=I) T' hy h2) hx0).trans ?_
  change s*x ≤ 2*x*s; nlinarith
end trace

namespace Donor
local notation "Xp" => T.a
local notation "Xq" => hat R.L x
local notation "Dk" i:max => dleaf R.L (Xq i)
 
variable {F0 : Scrolls B}

def shapeMass (T:Month x 1 6 2 N0 V W) (i:ℕ) : ℝ :=
  (2*(strip (hat R.L x i)*jumpCost V (T.a i)) + 3*dleaf R.L (hat R.L x i))*postage B R.L i

def volumePrice (T:Month x 1 6 2 N0 V W) (i:ℕ) : ℝ := earnings W (T.a i) (2*hat R.L x i) (dleaf R.L (hat R.L x i) / 1000)*postage B R.L i

def horizontalPrice (T:Month x 1 6 2 N0 V W) (i:ℕ) := 2*|shapeMass T i| * 2^(i+2)

lemma pace_shape (r : ℝ) (i:ℕ) :
    Record.paceZ (T.a i) (cell m B R.L i) K.top.clip K.top.paths (strip (Xq i)*r) ((Dk i)*r) =
      shapeMass T i*r*game m := by
  unfold Record.paceZ
  rw [jump_account (V:=V)]; unfold Graph.Diff.rankV; change _ + 3 * (_*sites (cell m B R.L i)) = _
  rw [sites_postage]; unfold shapeMass; ring

-- Price after dividing out offsets
lemma price_formula (i:ℕ) : earnings W (Xp i) (2 * Xq i) (Dk i / 1000)*sites (cell m B R.L i) = volumePrice T i * game m := by rw [sites_postage]; exact (mul_assoc ..).symm

variable (H : Service V U W J q h D C Q P N0 delay) {c : VolumeRate.Bet (trunkY n b)}
    (Y : Donor V b n N0 J q h D C Q T m ht W0 B0 f P F0)
    (a : Bon J q h D delay (Actual T ht W0 f (trunkY n b)))
    (Z : Solved P (Actual T ht W0 f (trunkY n b)) 0 c)
    (hp : 1≤h)
local notation "Zp" => Branch.gram P BT c
local notation "AC" i:max => (((Y.gram i).F,(Y.gram i).K) : Corr (Ω i))
include ht H a Z Y hp
private lemma transfer (i r:ℕ) (hi:i+r<buoy n) (s:Orbit (cell m B R.L i)) :
    ‖field U (Zp i) (W0 i) s-field U (Y.gram i) (W0 i) s‖ ≤
    2*(shapeMass T i * decline r * game m)*Real.exp (volumePrice T i * game m) := by
  obtain ⟨x,w⟩:= cooldown ht Y H Z a r i hi -- order
  let u:= (W.arm (T.large.trans ht) kT); let F:= Y.gram i
  have p:i < buoy n:=(by omega); have ht':i<kT:= p.trans (deeper ..); have hq:= a.clocks i; have hhi:= matched_of_enters hq (a.beta_ok H Z.toRealQ i ht'.le).2
  have hb1 : 0 ≤ (Zp i).beta ∧ (Zp i).beta ≤ 2* (Xq i) := ⟨le_trans (show 0 ≤ Xq i/2 from (by linarith [hq.grade])) hhi.1,hhi.2⟩
  have ht₂:= Y.pull.sift i ht'.le
  have hb2 : 0 ≤ F.beta ∧ F.beta ≤ 2*(Xq i) := ⟨le_trans (show 0 ≤ Xq i/2 from (by linarith [hq.grade])) ht₂.1,ht₂.2⟩
  have he:0≤ Dk i * decline r := mul_nonneg hq.leaf.le (by unfold decline; positivity)
  have hf:= (Y.cape i).paid; have hR : Roof (cell m B R.L i) J.k d J.n (W0 i) := {hf with paid:=fun z=>(hf.paid z).shrink J.hr.le}
  rw [Y.cool.represented i,←price_formula, ←pace_shape]
  exact transfer_record (a.charged H Z.toRealQ i ht'.le).toCost (Y.cool.charged _ p).toCost x w hp
    (div_nonneg hq.leaf.le (by norm_num)) he (u.sound i) hR (J.gran.trans (Y.cape i).size) hb1.1 hb2.1 hb1.2 hb2.2 _

omit Z a

/-- The horizontal estimate, valid at fixed pivot and for all realized pairs
in this election. `decay n (log 2)` here is `2 ^ (-K)` with K = `buoy n`, so
also sufficient for the price with `2 ^ (-K/2)`. Extensity on actual m scale.
No uniform threshold in m on election asserted. -/
theorem horizontal (i:ℕ) (hi:i<buoy n) {ρ : ℕ→ℝ}
    (A : Parcel J q h D C Q T ht W0 ρ f (trunk b n)) (pA : FromShot P delay A)
    (s:Orbit (cell m B R.L i)) :
    ‖field U (A.gram i) (W0 i) s-field U (Y.gram i) (W0 i) s‖ ≤
    horizontalPrice T i * decay n (Real.log 2) * Real.exp ((volumePrice T i+1) * game m) := by
  obtain ⟨a,b,Z,H',u⟩:= pA -- b shadows
  rw [H']; let r:=buoy n -(i+1); have hx:r+(i+1)=buoy n:= Nat.sub_add_cancel hi; let f:=game m
  have hf:0 ≤ f:=by unfold f game; positivity
  have ht':0 ≤ horizontalPrice T i:=by unfold horizontalPrice; positivity
  refine (transfer ht H Y a Z hp i r (by omega) s).trans ?_
  rw [decline_decay r (i+1),hx]; let z:= decay n (Real.log 2); let e:=Real.exp (volumePrice T i*f); let φ:=shapeMass T i
  have hg:0 ≤ z:= (decay_pos ..).le; have he:0 ≤ e:=(Real.exp_pos _).le
  rw [add_mul,one_mul,Real.exp_add]; change 2*(φ * (2^(_+_)* z)*f)*e ≤ horizontalPrice T i * z * (e * Real.exp f)
  calc
    _ ≤ 2*(|φ| * (2^(i+2)*z)*f)*e := by gcongr; exact le_abs_self φ
    _ = (horizontalPrice T i*z *e)*f := by unfold horizontalPrice φ; ring
    _ ≤ _ := calc _ ≤ (horizontalPrice T i*z*e)*Real.exp f := mul_le_mul_of_nonneg_left (le_trans (le_add_of_nonneg_right zero_le_one) (Real.add_one_le_exp f)) (by positivity)
                  _ = _ := by ring
end Donor
end LocalLimit
end YM.CF.Py.Rate

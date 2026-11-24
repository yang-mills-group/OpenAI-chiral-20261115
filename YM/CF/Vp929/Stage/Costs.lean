import YM.CF.Vp929.Stage.Preview
import YM.CF.Song.Crest
set_option autoImplicit false
set_option quotPrecheck false
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
open Eire Girt
open VolumeRate
variable {d:ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
variable {A C' Pay h ρ f ff ag Cg x β β' : ℝ} {D : Treaty J q A C' Pay h ρ} {c:Estimate}
variable {w:Location (R:=R) B m n} {p p' : BudgetPoint}
namespace Pitching
local notation "G5"=> SU.group
namespace Focus
open Tap Sour.MatchW Technique Stockpile Lilt Rill Haro Appel.Rate
open Sour Cycle929 Vow Larch
variable {n₀ n₁:ℕ}{b0 b1 b2 b3 Aχ Γχ r Wk:ℝ} (s: Major V Wk b0 b1 b2 b3 Aχ Γχ n₀) {pW:WindV K.j 2}
local notation "κS"=> rainX R 2 x
local notation "κB"=> rainX R 1 x
local notation "Υ"=> εp R Pay pW.C
local notation "P'"=> (K.top.clip)
local notation "Hd"=> K.below
local notation "nK"=> (Hd).paths
local notation "Qu"=> Tenant.quota^2
variable {κ κ0 Bv θ θ' ψ₁ ψ₂ γ Γ ξ ξ' :ℝ}{φ χ Zκ G Γk Kμ:ℝ→ℝ}(u:Outlook D c φ χ pW ag Cg Bv n₁)
local notation "Ls"=> (R.L.val:ℝ)
local notation "Yf" => εLeaf R.L
def earlyE (P C:ℝ):= 4 * Stockpile.march * majorTp P C
abbrev earlyT (W P C:ℝ) :=νC HI (catap W)*(2*earlyE P C)
def earlyR (K:Teller SU.group)(Aχ Γχ W P C:ℝ):=(tax_E HI K.top.clip K.below.width K.below.paths Aχ Γχ+1)* earlyT W P C
abbrev earlyQ (W P C:ℝ):= 4 * tiltB (catap W) HI * earlyE P C
local notation "Bκ"=> budS R Wk Pay pW.C
local notation "κR"=> (wrc R Wk Pay pW.C h)
local notation "τE"=> earlyE Pay pW.C
local notation "τT"=> earlyT Wk Pay pW.C
local notation "τQ"=> earlyQ Wk Pay pW.C
local notation "τR"=> earlyR K Aχ Γχ Wk Pay pW.C

lemma subsidy_X : ∀ᶠ x in atTop,(Scales.g SU.group R.L x)^2 ≤ Υ x:= by
 filter_upwards [tenor_Q (earlyE Pay pW.C *16/Ls) _ (subsidy_K R) (by unfold earlyE Stockpile.march; have hp:=lTp (R:=R) Pay pW.C; positivity)] with x p; refine p.trans_eq ?_; unfold earlyE εp r_T εLeaf; ring
lemma earnsL : Υ x = τE/Ls* Yf x:=by unfold εp earlyE r_T; ring
include s
lemma posEar : 0 < τE ∧ 0 < νC HI (512*Wk)∧ 0 ≤ tax_E HI K.top.clip K.below.width K.below.paths Aχ Γχ:= by
 refine ⟨(by unfold earlyE Stockpile.march; have hp:=lTp (R:=R) Pay pW.C; positivity), ?_, ?_⟩; · unfold νC; have he:= Py.desire HI (mul_pos (by norm_num : (0:ℝ) <512) s.ink); positivity
 rw [V.L.below]; exact money_K _ _ _ K.top s.air
lemma early (x:ℝ)(hX:(Scales.g SU.group R.L x)^2 ≤ Υ x)(hB: 0≤Υ x)(u0:1≤h) : Bκ x ≤ τT / Ls*(εLeaf R.L x) ∧ houseP (epoch x) K Aχ Γχ (Bκ x) ≤ τR /Ls * εLeaf R.L x ∧ τQ/Ls * εLeaf R.L x ≤ h^2 * κR x:=by
 obtain ⟨u,v,w⟩:= posEar (pW:=pW) (Pay:=Pay) s; let Z:=Scales.g SU.group R.L x
 have he: Bκ x≤ τT/Ls * Yf x:=by
    refine (mul_le_mul_of_nonneg_left (show εp R Pay pW.C x+(Z)^2 ≤ εp R Pay pW.C x+εp R Pay pW.C x from add_le_add le_rfl hX) v.le).trans_eq ?_; rw [earnsL]; unfold earlyT; ring
 refine ⟨he,?_ ,?_⟩
 · let V:= epoch x; have hz:=let_X HI x; let p_:= tax_E HI K.top.clip K.below.width K.below.paths Aχ Γχ; have ht:tax_E V K.top.clip K.below.width K.below.paths Aχ Γχ=p_:= spend_T HI _ _ _ _ _ V hz.1 hz.2.1 hz.2.2; unfold houseP; rw [ht]; refine (mul_le_mul_of_nonneg_left he (by exact add_nonneg w zero_le_one)).trans_eq ?_; unfold earlyR p_; ring
 unfold wrc Rtor Rone; rw [abs_of_nonneg hB,show h^2*(4 * _ * _ / h^2)= 4*tiltB (catap Wk) HI*(Υ x+(Z)^2) from ?_]; swap; · field
 rw [earnsL]; unfold earlyQ; let F:= tiltB (catap Wk) HI; have hh:0≤ F:= (Py.desire HI (mul_pos (by norm_num : (0:ℝ) <512) s.ink)).le; rw [mul_div_assoc (4* _), mul_assoc (4* _)]; apply mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) (mul_nonneg (by norm_num) hh)
lemma βcert : Chill_v (fun x=>phase_v (epoch x) (budS R Wk Pay C' x)):= qlop HI K.top s.direct (bud_f (R:=R)).2
end Focus
end Pitching
end YM.CF.Py.Rate

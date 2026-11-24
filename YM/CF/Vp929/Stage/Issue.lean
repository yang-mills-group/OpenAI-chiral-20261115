import YM.CF.Vp929.Stage.Stars
import YM.CF.Vp929.Stage.Tempos
import YM.CF.Vp929.Stage.Bundle
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

namespace Focus
open Sour.MatchW Sour.MatchW.Technique Cycle929 Tap Lilt Vow Ione Beau
open Sour Stockpile Test
local notation "Y"=> x+billX R.L
local notation "Γ"=> (3*dleaf R.L x)
local notation "ε"=> dleaf R.L x/1000
local notation "Θ"=> mid n B

variable {δ C: ℝ} {DC C₁ R0:ℝ→ℝ}
structure Capsule (R:Patch) (x:ℝ):Prop where
 warm: ∀ y:ℂ,enters (x+billX R.L) y → thinR R x y
 high : 0<dleaf R.L x
 tall : 0<dleaf R.L (x+billX R.L)
 lower: dleaf R.L (x+billX R.L) ≤ dleaf R.L x
 more : 1 ≤ x+billX R.L
 cold : strip (x+billX R.L) ≤ (x+billX R.L)/1000
variable (s:Capsule R x)
include s
lemma submits {F:Pair (Corr (mid n B))}{p':BudgetPoint} {b:ℂ}(t:enters (x+billX R.L) b)(V: Both (Charged p' w.input K.j R.L.val h (3*dleaf R.L x)) F): Client K R x w.input p' h b F:=⟨s.warm _ t,3*dleaf R.L x, (by unfold εLeaf; linarith [s.high]), V⟩
omit s
include V
lemma prolong (t:Chill_v DC)(h:∀ᶠ x in atTop,0 ≤ DC x) : ∀ᶠ x in atTop,Capsule R x:=by
 have he : 0 < billX R.L := mul_pos (Gauge.slopeConstant_pos Thera.yet_one) (Real.log_pos (by exact_mod_cast (show 1<R.L.val by have he:=V.tallX; omega)))
 obtain ⟨r,v⟩:= eventually_atTop.mp (eventual_prices (R:=R) he t h)
 filter_upwards [eventually_ge_atTop r,enters_eventually (R:=R)] with x p z; let H:= v x p; have hx:x ≤ x+ billX R.L:= le_add_of_nonneg_right he.le; let T:= v _ (p.trans hx); exact ⟨z,H.leaf,T.leaf,H.leaf_mono _ hx,T.grade,T.peri⟩
omit V
variable {s}
variable {r:ℝ} [Nonempty (ΘS r)]
namespace Shop
structure Ready (δ C:ℝ)(T:Shop w J p p' q h x r) :Prop where
 more : T.maxU ≤ dleaf R.L x/1000
 last : T.maxV ≤ dleaf R.L x /1000
 gold : T.maxΔ ≤ δ
 money : T.maxC ≤ C
variable (t:Shop w J p p' q h x r)(s:Capsule R x)(u:Ready δ C t)
local notation "G'"=> t.operate
local notation "Sch"=> Client K R x w.input p' h
local notation "jHt"=> t.A0.dream.floor
local notation "xT" => t.maxΔ
include t s u V
set_option maxHeartbeats 1500000 in
lemma worn : Certified V U W J q h x p p' r δ C w t.operate:=by
 have bΨ(b:ℂ)(F:Pair (Corr Θ))(q:Sch b F): Both (Charged p w.output K.j R.L.val h (ε)) ((G').arrays b F) ∧ ‖(G').Δ b F‖≤δ:=⟨t.taxed q u.more u.last,(t.careτ q).2.2.trans u.gold⟩
 have bA : ∀ (S:Set ℂ),IsOpen S → ∀ (b:ℂ→ℂ)(F:ℂ→Pair (Corr Θ)),(∀ z∈ S, enters (Y) (b z) ∧ Both (Charged p' w.input K.j R.L.val h Γ) (F z)) → DifferentiableOn ℂ b S → HoloCorr S F → HoloCorr S (fun z=> (G').arrays (b z) (F z))∧DifferentiableOn ℂ (fun z=>(G').Δ (b z) (F z)) S:= fun S q b F g w z=> t.RepTrail (Arcμ.mk q w z (fun i hi=> submits s (g i hi).1 (g i hi).2))
 refine ⟨fun b F X H=> bΨ _ _ (submits s X H), bA, ?_,?_⟩
 · intro b F v hb hF Z X; have pB:Sch (b:ℂ) (F,0):= submits s hb ⟨hF,Charged.zero.mono (mul_nonneg (by norm_num) s.high.le)⟩; obtain ⟨a,x,t₀,v',p'⟩:= t.RepReal pB v; have hp:0<r:= t.Th.radius; exact ⟨t₀,v',((norm_fst_le (t.pickW b (F,0))).trans (t.δV pB)).trans (by linarith),a,x.wear,p'.trans (mul_le_mul_of_nonneg_right u.money (zero_le_one.trans (sites_pos _)))⟩
 intro a c b b' F F' hv he hk hl hδ; obtain ⟨t,q⟩:= hv (b,F) (by simp); obtain ⟨t',w⟩:= hv (b',F') (by simp)
 exact fractions _ s.tall s.high (fun z A w u=> let H:= bΨ z A (submits s w u); ⟨⟨H.1.1.toCost,H.1.2.toCost⟩,H.2⟩) bA s.more (jHt) s.lower s.cold t t' q w he hk hl hδ
end Shop
end Focus
end Pitching
end YM.CF.Py.Rate

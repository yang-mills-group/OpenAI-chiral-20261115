import YM.CF.BProof.Push.Dream
import YM.CF.Ups.Tree
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Beau.PushA
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k' m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
open Ione
local notation "N"=> P.order
local notation "Xo"=>Skye.Seat n
open Ione Larch
open Taxi Geo RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
local notation "Hz"=> Scree.Hub n
open Trees
open Iva Lilt Salt Palot Floral Sour Haro Tap Sour.BondL Mew
open scoped YM.CF.Mew
open Reef Taxi.Denn
-- density glue. Conditional on exact real scalar gas equation for alpha and the standard input (which supplies beta, momentum & v₀ through Jade step). No division by a stateful kernel. (Private convention subtract L in actual hausse numerator - never double count P.alpha).
open Jade
variable {M B J:Side}{o:Odd J.val}{j:ℕ}{V:Pricing j J o (Vault.Thread j)} {e:ℝ}(U:Grasp V B e) (A:Scree.Loom (mid M B))(Q:GramM (mid M B)){v:Orbit (mid M B)}
variable {F H: RegBudget (mid M B)}{W₀ W₁:ForceBudget (mid M B)}{d₀ d₁ L₀ L₁:ℝ}{Z:Pane (mid M B)→ℝ}{K: Cusp (mid M B)}
private lemma tank_scale (Q:Op (Single n))(V:Cipher n)(t:ℝ):tank Q (t • V)=(↑t:ℂ) • tank Q V:=by unfold tank; rw [smul_sum]; apply sum_congr rfl; intro i _; change (t • crumb V.val i) • _=_; rw [Complex.real_smul]; exact mul_smul ..
lemma pressure (q:FleetS Q.p.threshold v.1)(g:picP Q.p K F W₀ Q.path Q.funds Q.beta d₀ L₀ 0)(h:picP Q.p K H W₁ Q.path Q.funds Q.beta d₁ L₁ Z)(u:ℂ) : denZ (spark_B Q H W₁ d₁ (u+ (L₁-L₀:ℝ))) U A v= Real.exp (Z v.1) • denZ (spark_B Q F W₀ d₀ u) U A v:=by
 let x(b:ℝ):= Q.path.inChannels Q.funds Q.p (Q.beta-b) v.1; let X:= spark_B Q F W₀ d₀ u; let Y:=spark_B Q H W₁ d₁ (u+(L₁-L₀:ℝ)); let A':=ink Q.p Q.path Q.funds Q.beta d₀ v.1; let B':= ink Q.p Q.path Q.funds Q.beta d₁ v.1; let s:=L₀+A'; let t:=L₁+B'-Z v.1; let D0:= X.board v; let D1:= Y.board v
 have hy (X:RegBudget (mid M B))(W:ForceBudget (mid M B))(c:ℝ)(w:ℂ): exp (exponentL Q.p X v.1)*fueled Q.p W v=(spark_B Q X W c w).board v:=by unfold GramM.board; rw [show (spark_B Q X W c w).slip=0 from rfl,Vale.still_Footprint,add_zero]
 have ht: Real.exp s • D0= Real.exp t • D1:=by have hs:=(g v q).symm.trans (h v q); rw [Pi.zero_apply,sub_zero,hy F W₀ d₀ u,hy H W₁ d₁ (u+(L₁-L₀:ℝ))] at hs; exact hs
 have he:D1= Real.exp (s-t) • D0:=by rw [Real.exp_sub,div_eq_inv_mul, mul_smul,ht,inv_smul_smul₀ (Real.exp_pos _).ne']
 let a:=X.betaL A v; let b:=Y.betaL A v; have hx:b+(↑(s-t):ℂ)=(Z v.1:ℂ)+a:=by unfold a b X Y s t A' B' ink GramM.betaL GramM.H0; dsimp only [spark_B,slew_e]; push_cast; ring
 change Complex.exp b • acts (tank (Dial.spar j X.J.M (A v)) D1) (relV U X.J (A v))= Real.exp _ • (Complex.exp a • _); rw [he,tank_scale,act_smul, smul_smul, Complex.ofReal_exp,←Complex.exp_add,hx,Complex.exp_add, ← Complex.ofReal_exp, ← Complex.coe_smul, mul_smul]
end YM.CF.Beau.PushA

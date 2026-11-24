import YM.CF.Vp929.Canon.Pest
import YM.CF.Vp929.Canon.Galley
import YM.CF.Milo.Soul
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.flexible false
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

open Taxi RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
namespace Test
namespace Plum
variable {P P':BudgetPoint}{K : Teller SU.group} {R : Patch} {L:ChartRatio SU.group}{V: Grace K R L}{d:ℝ}
variable {α:Side} {m B:Side}{U: Grasp V.U B d}
local notation "Ω"=> mid m B
variable {h h' c C σ a b β β' :ℝ}{η:Clip}{k:ℕ}
variable {R':PathData SU.group}{E F:Corr (mid m B)}{I:Interest (mid m B)}{A:Scree.Loom (mid m B)} {v v':ℂ}
local notation "X"=> construct P R' η I β E v
local notation "Y"=> construct P' R' η I β' F v'
def traceWater (y:Orbit Ω)(P:BudgetPoint)(F:Corr Ω)(R:Scree.Loom Ω)(I:Interest Ω):Cipher Ω:=exponentL P F.1 y.1 + Hest.boat (I.P.den (R y))
lemma sun_reader (y:Orbit Ω)(p:flags P.threshold y.1=∅)(g:U.roundZ ≤ (mid m B).val)(e:Guard (A y) d): denZ X U A y=Complex.exp ((X).betaL A y) • acts (tank (spar K.j I.M (A y)) (exp (traceWater y P E A I))) (changeM U (A y) I.M) :=by
 let PP:=spar K.j I.M (A y); let T:= (U.broadness _ g I.M).projection _ e;
 let Q:=exponentL P E.1 y.1; let W:= Hest.boat (I.P.den (A y)); let S:= (nursery PP T).cook
 unfold denZ GramM.board relV; dsimp only [construct]; rw [Vale.still_Footprint,add_zero,fuel_one _ _ _ p,mul_one]
 rw [←Hest.birth _ _ T,← Poly.rising]
 congr 1; change acts (S (exp Q)) (acts (S (exp W)) _) = acts (S (exp (Q+W))) _
 letI : NormedAlgebra ℚ (Cipher Ω):=NormedAlgebra.restrictScalars ℚ ℝ (Cipher Ω); rw [←act_mul, ← map_mul S,exp_add]
-- independent Stack at identity
lemma harvest_stack (P:BudgetPoint)(x: RegBudget α) : StackL x univ=orbitPH (exponentL P x 1):=by
 unfold StackL exponentL; rw [Sour.Glyph.ps_k]; refine sum_congr rfl fun i _=> Eq.symm (congrArg (fun W:Cipher α=>orbitPH W) ?_); exact Set.indicator_of_mem (ping_f P _) _
lemma trace_both (y:Orbit Ω)(p0:flags P.threshold y.1=∅)(p1:flags P'.threshold y.1=∅)(g:U.roundZ≤ (mid m B).val)(q:Guard (A y) d)(h:denZ X U A y=denZ Y U A y): let t:=spar K.j I.M (A y); (1-t)*orbitPH (exponentL P E.1 y.1)*t=(1-t)*orbitPH (exponentL P' F.1 y.1)*t:=by
 intro t; rw [sun_reader y p0 g q,sun_reader y p1 g q] at h; have he:= rootExp ((U.broadness _ g _).projection _ q) (Spire.sea_g g (A y) q I.M) h; unfold traceWater at he;
 simp only [Haro.orbP,add_mul,mul_add] at he; exact add_right_cancel he
lemma trace_agree (e:∀ y:Orbit Ω,FleetS P.threshold y.1→ FleetS P'.threshold y.1 → denZ X U A y=denZ Y U A y)(g:U.roundZ≤ (mid m B).val)(Q: Roof (mid m B) b h k A)(q:h ≤ d)(hp:P.threshold≤b):let t:=spar K.j I.M (1:Pane Ω); (1-t)*StackL E.1 univ*t=(1-t)*StackL F.1 univ*t:=by
 let y:Orbit Ω:=(1,Classical.arbitrary (Ids Ω)); have he:=e y (clear_identity P) (clear_identity P'); let g₀: flags P.threshold y.1=∅:=UVNext.CouplingReset.flags_one P; have ht:= (Q.paid y).shrink q; intro t; have hx:= trace_both y g₀ (UVNext.CouplingReset.flags_one P') g ht he
 rw [harvest_stack P E.1,harvest_stack P' F.1]; have hT:A y=1:=Vale.Grace.Robes.solar y A Q P hp g₀; simpa only [t,hT] using hx
-- Another exact observation of total Stack from PackSale specialization
open QuiltB Cycle929
lemma piece_stack {Zξ:Cusp α}{Q:RegBudget α}(p:Piece P h R' η Q Zξ a b c) : StackL Q univ=0:=by
 rw [harvest_stack P]; let y:Orbit α:=(1,Classical.arbitrary (Ids α)); rw [show (1:Pane α)=y.1 from rfl,p.quiet y (ping_f P _),Taxi.mon_v, Moto.hol_l]
end Plum
end Test
end YM.CF.Py.Rate

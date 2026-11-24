import YM.CF.Taxi.Mile
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Spin
import YM.CF.Taxi.Pout
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Taxi
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
open AnalyticBridge.VerifiedReset Push.Local Next.Foundations
open StressFlux Reef
private lemma roseC(u: Skye.Seat n)(c: PlaqAxes)(x:SU.group.Color): Reef.cloak _ ((AnalyticBridge.VerifiedReset.wedge c x).field u)=(AnalyticBridge.VerifiedReset.wedge c (Reef.frolic x)).field u:=by
 funext i; unfold Reef.cloak; simp only [ContinuousLinearMap.pi_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,wedge_field]; split_ifs; exact Reef.frolic.map_smul _ _; exact Reef.frolic.map_zero
lemma coeffEcho (o: Skye.Seat n) (X:Support (More n)) (F: Pane n→ ℝ)(T':P.Regular X F)(x y:PlaqAxes): AnalyticBridge.VerifiedReset.coeff (F ∘ echo) o x y= AnalyticBridge.VerifiedReset.coeff F o x y:=by
 let L:=Reef.cloak (Bond (More n)); let c:= AnalyticBridge.VerifiedReset.coeff F o x y; let f:= AnalyticBridge.VerifiedReset.germ F; let Z':= AnalyticBridge.VerifiedReset.spike SU.group; let w(i:PlaqAxes):=(AnalyticBridge.VerifiedReset.wedge i Z').field o
 have hv:f ∘ L= AnalyticBridge.VerifiedReset.germ (F ∘ echo):=by
    funext i; change F (increment 1 (L i))=_; apply congrArg; funext j; simp only [RG.increment,Reef.echo,Pi.one_apply,mul_one]; exact cool_a _
 let S:=Thera.yet_one; have hQ:logHessian F (L (w x)) (L (w y))=c:=by rw [roseC,roseC,label_color _ S T']; simp [Reef.frolic.norm_map, AnalyticBridge.VerifiedReset.spike_norm S,Z',c]
 have hx:= AnalyticBridge.VerifiedReset.germ_diff T'; have he:iteratedFDeriv ℝ 2 (AnalyticBridge.VerifiedReset.germ (F ∘ echo)) 0= iteratedFDeriv ℝ 2 (f ∘ L) 0:=by rw [hv]
 rw [jets_linear L (f:=f) (k:=2) (by exact hx)] at he
 let V0:=![w x,w y]
 have hz:=congrArg (fun i:(Directions SU.group (More n) [×2]→L[ℝ] ℝ)=>i V0) he
 change logHessian (F ∘ echo) (w x) (w y)= (iteratedFDeriv ℝ 2 f 0) (fun i=>L (V0 i)) at hz
 rw [show (fun i:Fin 2=>L (V0 i))=(![L (w x),L (w y)]:Fin 2→Directions SU.group (More n)) from funext fun i=>by fin_cases i<;>rfl] at hz
 exact hz.trans hQ
end YM.CF.Taxi

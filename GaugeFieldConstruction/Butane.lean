import YM.CF.Oath.Suit
import GaugeFieldConstruction.Hollow
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
open Feu Feu.Corset Haro
open Jet Plume Eire.Dress
variable {N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{G:Ratio (mid N B) (mid P B)}
-- MB unprojected single‐site tariff without EPA.WEST. Cost Strung across all Harper => value tariff independently of Ride: valid both touched and outside. Smaller inversion operator budgets.
abbrev Brush (p:Support (Domain P B)→Support (Domain P B)→Directions SU.group (Domain N B)→ Rock (mid N B)→Rock (mid N B)→Op SU.Slot)(J:Finset ((Support (Domain P B))×Support (Domain P B)))(y:Directions SU.group (Domain N B)) : FC (LeanV (Single (mid N B))) := ∑ i∈J, ∑ j:Rock (mid N B), ∑ k:Rock (mid N B),lineY j k (p i.1 i.2 y j k)
abbrev broomK (p:TailB→ Support (Domain P B)→Toll (Iota G))(Q:ℝ)(J:Finset ((Support (Domain P B))×Support (Domain P B)))(T':Support (Domain N B))(k:ℕ)(r s:Rock (mid P B)):Raid (Dwell (mid N B)):= ∑ i:Ride S, (mapK (S:=S) k p r s T' Q J) i
lemma brushMoney (p:Support (Domain P B)→Support (Domain P B)→Directions SU.group (Domain N B)→ Rock (mid N B)→Rock (mid N B)→Op SU.Slot)(Qx:TailB→ Support (Domain P B)→Toll (Iota G))(J:Finset ((Support (Domain P B))×Support (Domain P B)))(r s:Rock (mid P B))(T':Support (Domain N B))(Q:ℝ)(k m:ℕ)(b:∀ i∈J,∀ (a b:Rock (mid N B)),∀ x y:SU.Slot, Pence m (fun z=>p i.1 i.2 z a b x y) 0 (paintL G r a (Qx (true,true) i.1)*(paintL G s b (Qx (true,false) i.2)*Q))): Woody m (Brush p J) 0 (broomK (S:=S) Qx Q J T' k r s):=by
 let F(j:Ride S)(z:Directions SU.group (Domain N B)) := (∑ i∈J,curbY (S:=S) (Stilo.beamH T' ⊔ mark_l S k i.1⊔mark_l S k i.2) (p i.1 i.2 z)) j
 have hw(j:Ride S):= begets (k:=m) j r s Qx J p Q k T' (fun i w _ a v=> b i w a v) -- tune
 apply (Woody.sumV (S:=Finset.univ) (G:=F) (fun i _=> hw i)).germ -- s? capital S
 filter_upwards with y; rw [Finset.sum_apply]; unfold F; simp_rw [Finset.sum_apply]; rw [Finset.sum_comm]; unfold Brush; apply sum_congr rfl ; intro i v; simp [curbY,Pi.single_apply]
-- total
open Trees
lemma cleanPrice (p:BudgetPoint) (o:Site (Domain N B))(h:ℝ)(Qx:TailB→Support (Domain P B)→Toll (Iota G))(W:ℝ)(J:Finset ((Support (Domain P B))×Support (Domain P B)))(Z: Support (Domain N B))(b:ℕ)(r s:Rock (mid P B))(a k:ℕ)(f:ℝ)(hu:0≤p.threshold)(C:Strung Z (rateT (Scree.tariff p o h) (mapK (S:=S) b Qx r s Z W J)) k 0 f): joinV (Scree.tariff p o h) (broomK (S:=S) Qx W J Z b r s) ≤ f:=by
 have hc := C.pay; refine le_trans (le_of_eq ?_) hc; unfold broomK; let M:= mapK (S:=S) b Qx r s Z W J
 rw [joinVsum]; change _=∑ i:Ride S, currency k 0 (Stilo.bay i)*joinV _ ((mapK (S:=S) b Qx r s Z W J) i) ; simp [stampQ,Trees.currency, Hake.rateT]
end YM.CF.Oath
end

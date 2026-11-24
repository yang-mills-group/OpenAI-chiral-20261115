import YM.CF.Plume.Stream
import YM.SectorNext.VACUUM_NORMALIZATION.ForestLine
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Plume
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
variable {N P B:Side}(S:StepData (Domain N B) (Domain P B))(x:ℝ)
local notation "G₀"=> SU.group
local notation "n₀"=> (Domain N B)
local notation "m₀"=> (Domain P B)
local notation "Tabs"=>Arena.Tab S
variable{S}
open scoped Classical ENNReal NNReal
open Girt Next.Fluctuations.Sector Dial
-- explicit product induction over real.S.Team.
lemma calendar {E F W X:Type*}[Fintype E][Fintype F][Fintype W][NormedAddCommGroup X][NormedSpace ℝ X][Nonempty F](H:E→W→F→X)(a:ℝ): ((Fintype.card E:ℝ)⁻¹*a) • (∑ i:E,∑ w:W,∑ j:F,H i w j)= a • ((Fintype.card (E × F):ℝ)⁻¹ • (∑ i:E × F,(Fintype.card F:ℝ) • ∑ w:W,H i.1 w i.2)):=by
 let b:= (Fintype.card E:ℝ); let c:= (Fintype.card F:ℝ); let f(i:E):=∑ j:F,∑ w:W,H i w j
 have hc:c≠0:=by unfold c; positivity
 rw [←Finset.smul_sum (r:= (Fintype.card F:ℝ)), Fintype.sum_prod_type, Fintype.card_prod,Nat.cast_mul] -- nested inner and outer
 change _=a • ((b*c)⁻¹ • (c • ∑ i:E,f i))
 rw [smul_smul ((b*c)⁻¹), show (b*c)⁻¹*c=b⁻¹ from by rw [mul_inv_rev, mul_comm c⁻¹, mul_assoc,inv_mul_cancel₀ hc,mul_one], smul_smul, mul_comm a]; apply congrArg; exact sum_congr rfl fun i _=>sum_comm
end YM.CF.Plume

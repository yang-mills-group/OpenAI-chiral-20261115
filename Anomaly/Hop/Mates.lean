import Anomaly.Hop.Abode
/-!
 Transformer law at prepared poles. For geometric arrays with common Ψ s on such blocks, apply after STEM keys aggregated. No ownership assumptions on stabilizers are intended.
 -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew
variable {N n B:Side}
set_option autoImplicit false
open Mew Waxy

variable {P:Side}{l:Patch}{K:Teller SU.group}{L:ChartRatio SU.group}
  (V:Grace K l L) {e:ℝ}(P_:Grasp V.U B e)
  (G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(G₀:Scree.Loom (mid N B))(G₁:Scree.Loom (mid P B))(X:GramM (mid N B))(Y:GramM (mid P B))(Xp:Op SU.Slot)(q:Chi)(d h Vp Vf T W C BQ Rt Zt b g κp:ℝ) -- b,g∶ b call budgets all same, g Sized
variable {J: Type}[LinearOrder J][Fintype J]
open Oise Rive
open Ione.Clock
variable {I:Type}[Fintype I][LinearOrder I]
local notation "Tc"=> mid N B
open Vow.TreasuryFog Roots Sour
-- weight algebra.Combined births.Cov.
variable (σ:I→Site (mid N B)) (t:J→Site (mid N B)) (X₁:I→I→ℂ)(V₁:J→J→ℂ)(i:I)(j:J)
local notation "OΦ"=> Cube.node ∘ σ
local notation "OΨ"=> Cube.node ∘ t
local notation "GΦ"=> Roots.pipe_ζ (Cube.node ∘ σ) i
local notation "GΨ"=> Roots.pipe_ζ (Cube.node ∘ t) j
variable (s:Sweep (mid N B))
structure MatchPipe (T: Roots.pipe_ζ (Cube.node ∘ σ) i ≃ Roots.pipe_ζ (Cube.node ∘ t) j): Prop where
    atKey (k: Roots.pipe_ζ (Cube.node ∘ σ) i): Spire.payZ s (X₁ k i)= V₁ (T k) j
-- Proof from Clearl association. only when F sets have layout.S. enough even when issuance from prototype at move.Fr.Math.Matrix. combine downstream with ascent.L.G
variable (T': Roots.pipe_ζ (Cube.node ∘ σ) i ≃ Roots.pipe_ζ (Cube.node ∘ t) j)(p: MatchPipe σ t X₁ V₁ i j s T')
include p
lemma paymentPipeE (X:I→RegBudget (mid N B))(Y:J→RegBudget (mid N B))(t':∀ i:GΦ,passingR (mid N B) s (X i) (Y (T' i))) : passingR (mid N B) s (markerCore OΦ X₁ X i) (markerCore OΨ V₁ Y j):=by
 intro h v
 unfold markerCore; simp only [Finset.sum_apply,Pi.smul_apply,map_sum]; rw [←Finset.sum_coe_sort (pipe_ζ OΨ j),←Finset.sum_coe_sort (pipe_ζ OΦ i)]; symm; apply Finset.sum_equiv T' (by simp); intro i h
 rw [suit_cost,show V₁ _ j= _ from (p.atKey i).symm, t' i _ v] -- tune implicit numerals shadow h
lemma paymentPipeF (X:I→ForceBudget (mid N B))(Y:J→ForceBudget (mid N B))(t':∀ i:GΦ,passingF (mid N B) s (X i) (Y (T' i))) : passingF (mid N B) s (markerCore OΦ X₁ X i) (markerCore OΨ V₁ Y j):=by
 intro h v k
 unfold markerCore; simp only [Finset.sum_apply,Pi.smul_apply,map_sum]; rw [←Finset.sum_coe_sort (pipe_ζ OΨ j),←Finset.sum_coe_sort (pipe_ζ OΦ i)]; symm; apply Finset.sum_equiv T' (by simp); intro i w
 rw [suit_cost,show V₁ _ j= _ from (p.atKey i).symm, t' i h v k]
lemma paymentPhase (X:I→ℂ)(Y:J→ℂ)(t':∀ i:GΦ,Y (T' i)=Spire.payZ s (X i)): Spire.payZ s (markerCore OΦ X₁ X i)= markerCore OΨ V₁ Y j:=by
 let F:= Spire.payZ s
 have ht(a b:ℂ): Spire.payZ s (a • b)=Spire.payZ s a • Spire.payZ s b:=by unfold Spire.payZ; cases Spire.wageZ s <;> simp [cSignX]
 have hu{C:Type}(L:Finset C)(F:C→ℂ):Spire.payZ s (∑ i∈L,F i)=∑ i∈L,Spire.payZ s (F i):=by unfold Spire.payZ; cases Spire.wageZ s <;> simp [cSignX]
 unfold markerCore; rw [hu,←Finset.sum_coe_sort (pipe_ζ OΦ i),←Finset.sum_coe_sort (pipe_ζ OΨ j)]; exact Finset.sum_equiv T' (by simp) fun k _=> by rw [ht,p.atKey k,t' k]
lemma arcPose (X:I→ArcΦ)(Y:J→ArcΦ)(u:s∈Whirl (mid N B))(U:UNI SpinIdx)(t':∀ i:GΦ,Y (T' i)= arc_s s.s U (X i)):arc_s s.s U (markerCore OΦ X₁ X i)= markerCore OΨ V₁ Y j:=by unfold markerCore; rw [color_rum,←Finset.sum_coe_sort (pipe_ζ OΦ i),←Finset.sum_coe_sort (pipe_ζ OΨ j)]; exact Finset.sum_equiv T' (by simp) fun k _=> by rw [colorD s u,p.atKey k,t' k]
end YM.CF.QuadClock

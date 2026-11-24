import YM.CF.Song.Tree
import YM.CF.Song.Fish
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
open Sour Haro Ione Larch Nor Prism Salt Beau
abbrev treeΘ {X:Side}(P:BudgetPoint)(L:ℕ):Finset (Scree.Hub X):= univ.filter fun i=> Pave P L i.val.2
lemma plea (n:Side)(P:BudgetPoint)(L:ℕ) : liveB ((treeΘ P L):Finset (Scree.Hub n)):=by
    intro s; ext i'; obtain ⟨j,rfl⟩:= (scope_q s).surjective i'; rw [mem_image]; constructor
    · rintro ⟨j',p,e⟩; change moveHub s j'= _ at e; rw [←e]; exact mem_filter.mpr ⟨mem_univ _,(dawnZ ..).1 ((mem_filter.mp p).2)⟩
    intro p; exact ⟨j,mem_filter.mpr ⟨mem_univ _,(dawnZ ..).2 ((mem_filter.mp p).2)⟩,rfl⟩
lemma teal (n:Side)(P:BudgetPoint)(L:ℕ)(v:4 ≤ L)(i:Scree.Hub n)(p:coverNumber P.B i.val.2 ≤1): i∈treeΘ P L:= mem_filter.mpr ⟨mem_univ _,lt_of_le_of_lt (pow_le_pow_left' p 3) (by change 1^3<L; simp; omega)⟩
end YM.CF.Py

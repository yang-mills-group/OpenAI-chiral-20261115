import YM.CF.Pso.Pick
import YM.CF.BProof.Floral.Baker
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oise
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
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p1 p2 p3 p4:ℝ}
open Cascade
open Fief
variable {X: Interest (mid N B)}{Y:Interest (mid P B)}{U: Grasp V.U B d}{W:GivenX V U}
variable (M: Sheep V U W G Y X k n A)
open Corne
variable {ρ α γ:ℝ}{F:Pilot}{Z:Pluck R}{P₁ P₂:BudgetPoint}
open Girt Eire
variable{H₀: GramM (mid P B)}{H₁:GramM (mid N B)}{G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)}{pK L':ℝ}{q q':Chi}{H:Muster G S x d T}
open YM.CF.Floral
open scoped YM.CF.Mew
variable {D:Set ℂ}(Xo Yo:D→ RegBudget (mid P B))(Zo:D→ForceBudget (mid P B))(Jk:D→ℂ)
local notation "P0" i:max=> color_b H₀ β (Xo i) (Yo i) (Zo i) (Jk i)
variable (oP:∀ i y,SubHol D fun z=> Xo z i y)(vP:∀ i y,SubHol D fun z=> Yo z i y)(cP:∀ i y,SubHol D fun z=> Zo z i y)
include oP vP cP
lemma olive_Ω (Mk:Monk SU.group S) (u:Ids (mid P B))(i: Rust (mid P B)):SubHol D fun z=> OpK S x (P0 z) Mk u T q d k i:=by
 let R0:=color_b H₀ β 0 0 0 0; let ξ(y):= guardB S x R0 Mk T q d k y; let X:= Mk.sent x T q d k β
 cases i with
 | inl i=>
    let Y:=i.1.val.2; by_cases p:warmY S R0 Mk Y; swap
    · have he(z:D):¬warmY S (P0 z) Mk i.1.val.2:=p; change SubHol _ (fun z=> sheer S x (P0 z) Mk T q d k i); unfold sheer; dsimp only; simp_rw [he,if_false]; exact SubHol.constant _ -- change _ issues
    let g:= ξ Y
    have he(z): sheer S x (P0 z) Mk T q d k i = g • (exp (if i.2 then Xo z i.1 X else Yo z i.1 X) -1):= if_pos (show warmY S (P0 z) Mk Y from p)
    have hl:SubHol D (fun z=>if i.2 then Xo z i.1 X else Yo z i.1 X):=by split; exact oP ..; exact vP ..
    change SubHol _ fun z=> sheer S x (P0 z) Mk T q d k i; simp_rw [he]; exact (hl.exp.sub (SubHol.constant _)).comp (fun x=>g • x) (differentiable_id.const_smul g)
 | inr i=>
    let Y:= i.val.1.val.2\i.val.2; by_cases p:warmY S R0 Mk Y; swap
    · have he(z:D):¬warmY S (P0 z) Mk Y:=p; have ht(z): shineK S x (P0 z) Mk u T q d k i=0:= if_neg (he z); change SubHol _ fun z=> shineK S x (P0 z) Mk u T q d k i; simp_rw [ht]; exact SubHol.constant _
    let g:=ξ Y; have he(z): shineK S x (P0 z) Mk u T q d k i =g • Zo z i (X,u):= if_pos (show warmY S (P0 z) Mk Y from p)
    change SubHol _ fun z=> shineK S x (P0 z) Mk u T q d k i; simp_rw [he]; exact (cP ..).comp _ (differentiable_id.const_smul g)
end YM.CF.Oise

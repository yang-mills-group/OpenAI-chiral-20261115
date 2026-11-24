import YM.CF.Ups.Tot
set_option autoImplicit false
set_option maxHeartbeats 980000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars true
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Jade.Earn
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
variable (F:Pilot)(Z:Pluck R) (I: Stake.Isle){σ:ℝ}(Q: Tun I Z F σ){H:Muster G S x d T}
variable {U:Grasp V.U B d}{W:GivenX V U}{X: GramM (mid N B)}{Y: GramM (mid P B)}(M: Sheep V U W G Y.J X.J (k+2) n A)(P_:∀ X: Support (Domain P B),Lend P B d X)
lemma bankCurrency (p: (1,1)∈Rent0 G d): ‖shipA G U Y.J.M Y.J.P.den Y.J.I X.J.I (1,1)‖≤ Fintype.card (Site (Domain P B))*M.height:=by
 obtain ⟨X,u,v⟩:=M.lake.members
 have ht(j:Site (Domain P B)): (∑ i∈ hit0 j, X i) ≤ M.height := ((sum_le_sum (fun i _=> le_mul_of_one_le_left (u i).pos (rent_one M.hs.le _)))).trans (v j)
 rw [M.lake.even _ p]; apply (norm_sum_le ..).trans
 calc
    _ ≤ ∑ i,X i:=sum_le_sum fun i _=> (u i).sumline _
    _ ≤ ∑ i:Seal (Site (Domain P B)),∑ j:Site (Domain P B),if j∈i then X i else 0:=by
       refine sum_le_sum fun i _=>?_; by_cases h:X i=0; rw [h]; simp
       obtain ⟨j,h⟩:= populated ((u i).travel h); apply le_trans (b:=if j∈ i then X i else 0) (by rw [if_pos h]); exact single_le_sum (fun j _=> ite_nonneg (u i).pos le_rfl) (mem_univ _) -- hp
    _ ≤ ∑ _: Site (Domain P B), M.height:=by rw [sum_comm]; refine sum_le_sum fun i _=>?_ ; rw [←sum_filter]; exact ht i
    _ = _:=by rw [sum_const,card_univ,nsmul_eq_mul]
end YM.CF.Jade.Earn

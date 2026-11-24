import YM.CF.Yaw.Sera
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Yaw
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Eire Jet Scroll Push.AbsoluteSums.Trees PetalP
variable {I N P B:Side}(S:StepData (Domain N B) (Domain P B)) (G:Ratio (mid N B) (mid P B)){r d k l D:ℕ}
open Rush Scroll Paige Vault Phase Acorn Spire
variable {ι:Type}[Fintype ι][DecidableEq ι](X:ι→ Palot.leaf (Site (Domain N B)))
local notation "m"=> mid P B
local notation "V'"=> Domain P B
local notation "H_"=> Eire.Ride S
local notation "S_"=> Eire.Folk S r ι
local notation "τ"=> Oboe (Single (mid P B))
local notation "χ"=> (LeanV (Single (mid P B)))
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
variable{S G}
variable (L:List (Kite S r))(U:List (Rust (mid P B)))(W:List ι)
local notation "Z'"=> weave_g L U W
open Eire Dress
variable {e A Q:ℝ}(R:GramM (mid P B))(M:E→Monk SU.group S)(T: ∀ i:E, Dress G S e r D (M i) R k X)
variable (x:ℝ)(l:ℕ)(C:Raid (LeanV (Single (mid P B))))
abbrev postY{n:Type}[LinearOrder n][Fintype n](A:Finset n)(C:Raid n):PetalP n:= ⟨{i:Finset n//i∈ Wheat A},inferInstance,fun i=> Finset.sort i.val (· ≤ ·),fun i=> C i.val ⟩ -- sort order
variable {C}
lemma stable(A:Finset χ)(F:E→FC (LeanV (Single (mid P B))))(z:E)(h: Woody l F z C)(p:∀ x,Flour A (F x)) : Meant z l (postY A C) put F:=by refine ⟨fun i y=>crumb (F y) i.val,fun i=>h.haveP _,Eventually.of_forall fun i=> Eq.trans (p i).pin ?_⟩; trans ∑ j:(Wheat A), crumb (F i) j.val • poke j.val; exact (sum_coe_sort ..).symm; rfl -- tune
abbrev boast (C:Rust (mid P B)→ Raid (LeanV (Single (mid P B))))(i:Folk S r ι): PetalP χ:=match i with
 | .inr (.inl j) => postY (camp (rustL (mid P B) j).val.2) (C j)
 | _=> PetalP.bud _
variable (f:Rust (mid P B)→ Raid (LeanV (Single (mid P B))))(z:E)
local notation "κ_"=> (Z').toFinset
lemma canon(c:ℕ)(h:∀ i∈ U, Woody c (fun y:E=>(schoolK X R M T x l (Z').toFinset (sentR i) y).val) z (f i))(i:S_)(g:i∈weave_g L U W): Meant z c (boast f i) put (fun y=> (schoolK X R M T x l (Z').toFinset i y).val):=by
 rcases i with i|i; · exact singletonK ..
 rcases i with i|i; swap; · exact singletonK ..
 apply stable c _ _ z (h i ((by simpa [←left_v (L:=L) (U:=U) (W:=W)] using mem_toLeft.mpr (mem_toRight.mpr (List.mem_toFinset.mpr g)): i∈ U)))
 exact fun y=> witnessH _ _ _ _ _ _ _ _ _ (T y).copies i -- n m
end YM.CF.Yaw

import YM.CF.Eire.Book
import YM.CF.Eire.Pearl
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Eire
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(x:ℝ)(e_:ℝ)(r l k D:ℕ)
local notation "bay"=> Stilo.bay
variable {ι:Type}[Fintype ι][DecidableEq ι](X:ι→ Palot.leaf (Site (Domain N B)))
open Rush Scroll Paige Vault Phase Acorn Spire
namespace Dress
variable {S G D k r l x}
variable (M:Monk SU.group S)(R:GramM (mid P B))
variable {M R X e_}
variable (U:Dress (r:=r) G S e_ D M R k X) -- order inferred?
variable (x:ℝ)(l:ℕ)
local notation "B₀"=> BranchX S X k
local notation "Fh"=> flags (temp x) M.V
local notation "O'"=> capG S Fh (chillB M) R.p.threshold
-- charged SCALAR Heir split.R.Phase law.JM.
-- exact table reassignment at arbitrary multipliers, stays conditional on material nonzero
variable {A:Stores S}{Z:Finset (Kite S r)}
local notation "κ"=> quaint (r:=r) (ι:=ι) (S:=S) (M:=M) (R:=R)
def coversY (A:Stores S): Finset (Finset (Rust (mid P B))):= univ.filter fun i=> rendL i.toRight= brushK A (chillB M) R.p.threshold ∧ Set.PairwiseDisjoint (i.toRight:Set (Force (mid P B))) (fun x=>x.val.1.val.2)
abbrev mic(A:Stores S)(X:Finset (Kite S r)):= paint S D U.pens U.dyes (U.blocks A).val.1.1 (U.blocks A).val.2 U.cloth X U.wager
lemma cent_l (A:Stores S)(Y: Finset (Kite S r))(X:Finset (Rust (mid P B)))(Q:Finset ι): (Y.disjSum (X.disjSum Q)) ∈ κ A ↔ Y∈ crewL S (blip S A r) ∧ X∈ coversY (M:=M) (R:=R) A:=by
 rw [lightP]; simp only [coversY,quaint,mem_filter,mem_univ,true_and,penn,toLeft_disjSum, earn,toRight_disjSum]; aesop -- tune
local notation "ζ"=> coversY (M:=M) (R:=R)
lemma quill (A:Stores S)(p:A.flags=flags (temp x) M.V): (∑ i∈ κ A,(U.sweepG x l i).val)= issue (U.stalk A) (∑ i∈ coversY (M:=M) (R:=R) A,(U.hiveB x l A i).val) (∑ i∈crewL S (blip S A r),U.mic A i)*(U.brood A).val:=by
 let D':=U.sweepG x l; let F(Q):= Q∈κ A; let V:= U.mic A; let G:= ζ A; let L:= crewL S (blip S A r); let R':= U.stalk A; change ∑ i∈ κ A,(D' i).val= issue R' _ _ *_
 have he: (∑ i:Troupe S r ι,if F i then (D' i).val else 0)=∑ i∈ κ A,(D' i).val:=by rw [←sum_filter]; congr; ext; simp [F]; -- tune
 rw [←he,breed]; let J(X:Finset (Kite S r)):=issue R' (∑ i ∈ G,(U.hiveB x l A i).val) (V X)*(U.brood A).val
 rw [show ∑ i:Finset (Kite S r), ∑ j:Finset (Rust (mid P B)⊕ι), _ =∑ i:Finset (Kite S r), if i∈L then J i else 0 from ?_]; swap -- hide Side P Shadow
 · refine sum_congr rfl fun i _=>?_ ; rw [breed]; by_cases h:i∈L; swap
   · rw [if_neg h]; exact sum_eq_zero fun j _=> sum_eq_zero fun w _ => if_neg fun v=> h ((cent_l A i j w).mp v).1
   rw [if_pos h]; unfold J; rw [map_sum,LinearMap.sum_apply,sum_mul]; unfold G coversY; rw [sum_filter]; apply sum_congr rfl; intro j _; by_cases t:j∈ coversY (M:=M) (R:=R) A; swap
   · rw [if_neg (fun p=> t (mem_filter.mpr ⟨mem_univ _,p⟩))]; exact sum_eq_zero fun w _=> if_neg fun v=> t ((cent_l A i j w).mp v).2
   rw [if_pos (mem_filter.mp t).2]; have ht(w:Finset ι):F (i.disjSum (j.disjSum w)):= (cent_l A i j w).mpr ⟨h,t⟩; simp_rw [if_pos (ht _)]; exact port_p U x l h j ht p
 rw [←sum_filter,filter_mem_eq_inter,univ_inter]; unfold J; rw [←sum_mul, ←map_sum]
end Dress
end YM.CF.Eire

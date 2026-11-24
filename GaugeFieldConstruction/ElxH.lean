import GaugeFieldConstruction.ValiseX
import GaugeFieldConstruction.Jupa
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry 
section mono
variable {α I M:Type}[LinearOrder I][Fintype I][DecidableEq α]
variable {σ:I→α}
abbrev carR (z:Key I)(l:List I):ℂ:= (l.map z).prod
lemma stack_bank (l:List I):River (fun z:Key I=>carR z l):= by
 induction l with
 | nil=> exact zeroR _
 | cons i l ih=> exact (show River (fun z:Key I=> z i) from north_r i).mul_T ih -- tune identifier
lemma arc0 [NormedAddCommGroup M][NormedSpace ℂ M][CompleteSpace M](l:List I)(x:M): River (fun z:Key I=> carR z l • x):= prodR (ContinuousLinearMap.lsmul ℂ ℂ) (stack_bank l) (zeroR x) -- tune
lemma stack_eq (l:List I)(v:ψS σ l)(z:Key I):carR z l=Mew.pine l.toFinset z:=by
 induction l with
 | nil=> simp[carR,Mew.pine]
 | cons a l ih=>
    have he:= (List.nodup_cons.mp (List.Nodup.of_map σ v)).1; have ht:ψS σ l:=(List.nodup_cons.mp (show List.Nodup _ from v)).2
    rw [Mew.pine,List.toFinset_cons,Finset.prod_insert (by simpa using he)]; change _*carR z l=_; rw[ih ht]
-- $carR ign when two ($u≠v$ possibly distinct index from same group)
lemma carR_zero (l:List I)(h:¬ψS σ l) : Kin σ (fun z:Key I=>carR z l) 0 :=by
 have e:GJ.stalk l (1:ℂ)=fun z:Key I=> carR z l:=funext fun z=>by simp [GJ.stalk,carR]
 rw [←e]; exact ⟨stalkR ..,zeroR _,fun i hi=> (noStem σ _ i h hi 1).trans (tip_0 i).symm⟩
end mono
end YM.CF.Scree.Ing
end

import GaugeFieldConstruction.CannonJ
import GaugeFieldConstruction.EraJ
import GaugeFieldConstruction.SambaJ
import GaugeFieldConstruction.OromoJ
import GaugeFieldConstruction.FrijaJ
import GaugeFieldConstruction.Gloss
import GaugeFieldConstruction.QuishJ
import GaugeFieldConstruction.NorasJ
import GaugeFieldConstruction.TributoJ
import GaugeFieldConstruction.AmusaJ
import GaugeFieldConstruction.SpursJ5
import GaugeFieldConstruction.Frosts
import GaugeFieldConstruction.Legends
import GaugeFieldConstruction.Frosts
import GaugeFieldConstruction.Swirls
import GaugeFieldConstruction.Infar
import GaugeFieldConstruction.Moll
import GaugeFieldConstruction.Panther
import GaugeFieldConstruction.Kenko
import GaugeFieldConstruction.HopeQ
import GaugeFieldConstruction.Overland
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 290000
set_option maxRecDepth 4000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
namespace Pitching
open Lich Iva
open Engine Engine.Basin Engine.Docket Dialect
open Vow Bake Salt Stax Sour Larch
namespace Focus
open Appel.Rate Stockpile
section
open Sour.MatchW Sour.MatchW.Technique Cycle929 Tap Lilt
open Next.Fluctuations.Sector
open Neon
open QuadClock Haro
open Mew Vow Rive Bake
open scoped YM.CF.Mew
open Riant
open YM.CF.Oath.BellPrice PinRack
open TableF TableF.Boom Lenten Layout Fren
section
open Mew Roots Connect Ing Ing.Iona CoeffArc Frugal
variable {I O A Y:Type}[Fintype I][LinearOrder I][Fintype O][LinearOrder O][DecidableEq A][Fintype A][DecidableEq Y][Fintype Y]
variable {L: Side}{K:Teller SU.group}{R:Patch}{N m n B:Side}{d vH x:ℝ}
variable {c:ChartRatio SU.group}
open Directory
namespace Onwards
open Larch Roots.GJ Ing Ing.Iona
variable {m B:Side}(Nkey:ℕ)(C:ℝ) {p:BudgetPoint}(σ:I→Seat N)(A:Finset I)
variable (w:I→I) (v:∀ i∈A,σ (w i)=σ i) (q:Set.InjOn w (A:Set I)) (s: ∀ i∈A,w i∉ A)
abbrev MatD (i j:I):ℂ:=if j∈A ∧ i=w j then 1 else 0
def reflux(i j:I):ℂ:= (if i=j then 1 else 0)- MatD A w i j

abbrev Stoop (i:I):=A.filter fun k=> i=w k
include v
lemma Λ_num (i:I): Stoop A w i ⊆ pipe_ζ σ i:= fun j h=>mem_filter.mpr ⟨mem_univ _,(v j (mem_filter.mp h).1|>.symm.trans (congrArg _ (mem_filter.mp h).2.symm))⟩
lemma Χpose (u:Key I)(i:I): toV_C σ (reflux A w) u i=u i - ∑ j∈ Stoop A w i,u j:=by
 unfold toV_C reflux; simp_rw [sub_mul,MatD] -- use ite_mul not mul
 simp only [ite_mul,one_mul,zero_mul,sum_sub_distrib]; congr 1
 · rw [sum_eq_single_of_mem (s:=pipe_ζ σ i) i (mem_filter.mpr ⟨mem_univ _,rfl⟩), if_pos rfl]; exact fun j _ u=> if_neg u.symm
 simp_rw [←sum_filter]; apply sum_congr _ (fun _ _=>rfl); ext j; simp only[mem_filter,Stoop]; exact ⟨And.right, fun h=>⟨mem_filter.mp (Λ_num σ A w v i (mem_filter.mpr h)),h⟩⟩ -- tune mem_filter order
include s q
lemma Cost_P (i:I): ∑ j: Roots.pipe_ζ σ i, ‖reflux A w i j.val‖≤2:=by
 let J:=pipe_ζ σ i; rw[Finset.sum_coe_sort J (fun j=> ‖reflux A w i j‖)]; unfold reflux; apply le_trans (sum_le_sum (g:=fun j=>‖(if i=j then (1:ℂ) else 0)‖+‖MatD A w i j‖) (fun j _=>norm_sub_le ..)) _
 rw[sum_add_distrib,sum_eq_single_of_mem (s:=J) i (mem_filter.mpr ⟨mem_univ _,rfl⟩),if_pos rfl,norm_one]; swap; intro j h t; rw[if_neg t.symm,norm_zero]
 let D:=Stoop A w i; by_cases hp:D.Nonempty; swap
 · rw [sum_eq_zero (s:=J) (f:=fun j=>_) (fun j h=>show ‖MatD A w i j‖=0 from (by rw[MatD,if_neg (fun t:j∈A ∧ i=w j => hp ⟨j,mem_filter.mpr t⟩),norm_zero]))]; norm_num
 obtain ⟨a,h⟩:=hp
 let t:= J.filter fun j=> j∈A ∧ i=w j; rw[sum_eq_single_of_mem (s:=J) a (Λ_num σ A w v i h), MatD,if_pos (mem_filter.mp h),norm_one]; · norm_num
 intro j p hj; rw [MatD,if_neg (fun u:j∈A ∧ i=w j=>hj (q u.1 (mem_filter.mp h).1 (u.2.symm.trans (mem_filter.mp h).2))),norm_zero] -- orientation t Type.
section
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
variable (F: Finset I→ E)
omit v s q
lemma crafted (j:I)(p:j∉ A):Verdante σ (reflux A w) F {j}= F {j}:=by
 rw[aloneX]; simp_rw [reflux,MatD]; simp only [p,false_and,↓reduceIte,sub_zero]; rw [sum_eq_single_of_mem (s:=Roots.pipe_ζ σ j) j (mem_filter.mpr ⟨mem_univ _,rfl⟩),if_pos rfl,one_smul]; exact fun i _ v=> by rw[if_neg v,zero_smul]
include v
lemma Crafted (j:I)(p:j∈ A) : Verdante σ (reflux A w) F {j}= F {j}-F {w j}:=by
 rw[aloneX]; simp_rw [reflux,MatD,sub_smul,sum_sub_distrib]; congr 1
 · rw [sum_eq_single_of_mem (s:=Roots.pipe_ζ σ j) j (mem_filter.mpr ⟨mem_univ _,rfl⟩),if_pos rfl,one_smul]; exact fun i _ v=> by rw[if_neg v,zero_smul]
 rw [sum_eq_single_of_mem (s:=Roots.pipe_ζ σ j) (w j) (mem_filter.mpr ⟨mem_univ _,v _ p⟩),if_pos (show j∈A ∧w j=w j from ⟨p,rfl⟩),one_smul]; exact fun i _ v=> by rw[if_neg (fun h:j∈A ∧ i=w j=>v h.2),zero_smul] -- tune
end
#print axioms Cost_P
end Onwards
end
end
end Focus
end Pitching
end YM.CF.Py.Rate
end

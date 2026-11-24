import YM.CF.Sour.Lead
import YM.CF.Sour.Park
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
-- five bilinear.Glyph.Seat.Seam
variable (h:ℝ)(hx:1≤h)
abbrev coreK(i j:JS):FC (Dwell n):= if i=j then 1 else 0
include hx
lemma oreV (n:Side) : Glyph (n:=n) (fun A:Op (Single n)=> Matrix.trace A • 1) coreK h:=by
 refine ⟨fun A=> ?_,fun i j=> ?_,fun S i j p t=>?_,fun g K=> ?_⟩
 · unfold coreK; simp only [apply_ite _ _,smul_zero,sum_ite_eq,mem_univ,ite_true, Matrix.trace, Finset.sum_smul]; rfl
 · unfold coreK; split; refine ⟨by positivity,fun X=> le_trans ((Ark.one h).tubes X) (mul_le_mul_of_nonneg_right (one_le_pow₀ hx) (pow_nonneg (zero_le_one.trans hx) _)) ⟩; refine ⟨by positivity,fun i=>?_⟩; have hp:0 ≤ h:= zero_le_one.trans hx; simp; positivity
 · unfold coreK; split; exact Sector.one; exact Sector.zero _
 rw [trace_twist,sauce,singT,win_c,win_i,twist_scalar,map_one]; rfl -- ordering
lemma pal_v : Glyph (faceD true false) (fun i j:JS=> wire true i*wire false j) h:=by
 refine ⟨fun _=> rfl,fun i j=> by rw [sq]; exact Ark.opus h hx (Ark.blond (n':=Dwell n) h hx _) (Ark.blond h hx _),fun S i j p t=> Sector.mul (Sector.up (n:=Dwell n) (true,i) (mem_filter.mpr ⟨mem_univ _,p⟩)) (Sector.up (n:=Dwell n) (false,j) (mem_filter.mpr ⟨mem_univ _,t⟩)),fun g A=> (arm false false (tradew n g) A).symm⟩ -- tune
lemma less_k: Glyph (Sault.urn (trailM false) (trailM true)) (fun i j:JS=> trailM false i* trailM true j) h:=by
 refine ⟨fun _=> rfl,fun i j=>by rw [sq]; exact Ark.opus h hx (Ark.bud (n':=Dwell n) h hx _) (Ark.bud h hx _),fun S i j p t=> Sector.mul (Sector.down (n:=Dwell n) (false,i) (mem_filter.mpr ⟨mem_univ _,p⟩)) (Sector.down (n:=Dwell n) (true,j) (mem_filter.mpr ⟨mem_univ _,t⟩)),fun g A=> (boon false false (tradew n g) A).symm⟩ -- tune
lemma leg_k: Glyph (Sault.crib true) (fun i j:JS=>wire true i* trailM true j) h:=by
 refine ⟨fun _=>rfl,fun i j=>by rw [sq]; exact Ark.opus h hx (Ark.blond (n':=Dwell n) h hx _) (Ark.bud h hx _), fun S i j p t=>Sector.mul (Sector.up (n:=Dwell n) (true,i) (mem_filter.mpr ⟨mem_univ _,p⟩)) (Sector.down (n:=Dwell n) (true,j) (mem_filter.mpr ⟨mem_univ _,t⟩)),fun g A=> (dew false false (tradew n g) A true).symm⟩
lemma tail_k: Glyph (Sault.crib false) (fun i j:JS=> -(wire false j * trailM false i)) h:=by
 refine ⟨fun A=> ?_,fun i j=> ?_,fun S i j p t=>?_,fun g A=> (dew false false (tradew n g) A false).symm⟩
 · unfold Sault.crib; rw [gritz]; unfold Sault.urn; rw [sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; simp
 · let X:= wire (n:=JS) false j*trailM false i; have he:Ark X h (h^2):=by rw [sq]; exact Ark.opus h hx (Ark.blond (n':=Dwell n) h hx _) (Ark.bud h hx _)
   refine ⟨he.positive,fun k=>?_⟩; simp only [Matrix.neg_apply,norm_neg]; exact he.tubes k
 let X:= wire (n:=JS) false j*trailM false i; have ht:Sector (camp S) false X:= Sector.mul (Sector.up (n:=Dwell n) (false,j) (mem_filter.mpr ⟨mem_univ _,t⟩)) (Sector.down (n:=Dwell n) (false,i) (mem_filter.mpr ⟨mem_univ _,p⟩)); simpa using ht.scale (-1)
lemma fatR(F K T W R:Op JS): forge F K T W R=faceD true false K+Sault.crib true T+(Matrix.trace F • 1+Sault.crib false W)+Sault.urn (trailM false) (trailM true) R:=forkL ..
end YM.CF.Sour

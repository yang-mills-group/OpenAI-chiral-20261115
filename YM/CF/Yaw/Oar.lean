import YM.CF.Yaw.Flung
import YM.CF.Eire.Root
import YM.CF.Rill.Pools
import YM.CF.Rue.Pace
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
open Eire Jet Scroll
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(z:Odd G.count.val)(e:ℝ)(g:0<e)(X: Meter TailB G e)(V: Meter Grave G e)
local notation "bay"=> Stilo.bay
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
local notation "A'"=> Single (mid P B)
local notation "B'"=> Single (mid N B)
variable (K:E→Rill.Arch G e) (k:ℕ)
local notation "α'"=> Scion.tinOre (switchG G).symm
local notation "H'"=> Eire.Ride S
local notation "L'"=> Domain P B
local notation "W'"=> LeanV B'
abbrev mark_l (T:Support L'):= beamH (halo k (hatY S T))
abbrev gash(x:Rill.Arch G e)(i:Twig A')(j: LeanV B')(Y:Support L'):= Urn.mount (Radix G (fun s=>X s Y (bring g x))) (α' i) j
abbrev pairZ(x:Rill.Arch G e)(i j:Twig A')(Y:Support L'):= Urn.soar (oakN G fun v=>heal G e V v Y (bring g x)) (α' i) (α' j)
def due_z(i j:Twig A'):= Urn.soar (oakN G (feeX G)) (α' i) (α' j)
include z g
lemma miles(i:Twig A')(j: LeanV B')(x:Rill.Arch G e)(H:H'):
 (cala G S z e g X V x k H).seats i j=∑ Y∈ gleans S k H,gash G e g X x i j Y:=by
 change Urn.mount (LenT G e X (bring g x) _) (α' i) j=_; dsimp only [Urn.mount,LenT, Radix,marge,Matrix.submatrix_apply,id,gash]; split; swap; · rw [sum_const_zero]
 simp only [Matrix.sum_apply]; generalize (twigS _).1=b; cases b <;>simp only [cSignX,ite_true,Bool.false_eq_true,if_false,star_sum] -- tune generalize shape
lemma cryZ(i j:Twig A')(x:Rill.Arch G e)(H:H'):
 (cala G S z e g X V x k H).pals i j=(∑ Y∈ gleans S k H,pairZ G e g V x i j Y)+due_z G i j:=by
 change Urn.soar (KinG G e V (bring g x) _) (α' i) (α' j)=_; dsimp only [KinG,oakN, Urn.soar,pairZ,due_z]; split; simp
 simp only [Matrix.add_apply,Matrix.sum_apply]; generalize (twigS _).1=b; cases b <;>simp only [cSignX,ite_true,Bool.false_eq_true,if_false,star_sum,star_add]
-- emit arcs.b
abbrev balm (i:Twig A')(Y:Support L')(x:E):FC (LeanV B'):=∑ j:LeanV B', gash G e g X (K x) i j Y • put j
def fleetT(i:Twig A'):Track H' (E→FC (LeanV B')):=∑ Y:Support L',Pi.single (mark_l S k Y) (balm G e g X K i Y)
abbrev bowZ(i j:Twig A')(Y:Support L')(x:E):FC (LeanV B'):=pairZ G e g V (K x) i j Y • 1
def fleetZ(i j:Twig A'):Track H' (E→FC (LeanV B')):= (∑ Y:Support L',Pi.single (mark_l S k Y) (bowZ G e g V K i j Y)) + Pi.single ⊥ (fun _=> due_z G i j • 1)
lemma grants_m(H:H')(x:E)(i): lank (cala G S z e g X V (K x) k H).seats i=view H (fleetT G S e g X K k i) x:=by
 unfold fleetT lank; simp_rw [miles,Finset.sum_smul]; rw [sum_comm,show view H = ⇑(vAdd (Q:=E→ FC (LeanV B')) H) from rfl,map_sum]; simp_rw [show ∀ v:Track H' (E→FC (LeanV B')),vAdd H v=view H v from fun _=>rfl,singleV]; rw [Finset.sum_apply,gleans,sum_filter]; refine sum_congr rfl fun i _=>?_ ; unfold mark_l; split_ifs <;> rfl
lemma grants_z(H:H')(x:E)(i j): Stilo.price (cala G S z e g X V (K x) k H).pals (LeanV B') i j=view H (fleetZ G S e g V K k i j) x:=by
 unfold Stilo.price fleetZ; rw [view_add,Pi.add_apply,singleV,if_pos bot_le]
 rw [cryZ,add_smul]; congr 1; rw [show view H = ⇑(vAdd (Q:=E→ FC (LeanV B')) H) from rfl,map_sum]; simp_rw [show ∀ v:Track H' (E→FC (LeanV B')),vAdd H v=view H v from fun _=>rfl,singleV]; rw [Finset.sum_apply, Finset.sum_smul,gleans,sum_filter]; refine sum_congr rfl fun i _=>?_ ; unfold mark_l; split_ifs <;> rfl
end YM.CF.Yaw

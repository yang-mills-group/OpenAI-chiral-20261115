import YM.CF.Iva.Cart
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Iva
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
attribute [local instance] opCStarAlgebra
variable {E: Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]{x:E} {k:ℕ}
variable{n:Type*}[LinearOrder n][Fintype n]
local notation "Z₀"=> LeanV n
open Rue Font
variable{u v:ℂ}
abbrev cull_r (k:ℕ)(V:Toll n)(d:ℝ):Raid (LeanV n):=saber (cull k V d) 2
lemma chip_one (v:ℂ)(n:Type*)[LinearOrder n][Fintype n]:Pastry.hollow v= exp (0: Dough n)*Pastry.hollow v:=by rw [exp_zero,one_mul]
lemma horn_s(a b:ℂ):Pastry.hollow (n:=n) (a+b)=Pastry.hollow a+Pastry.hollow b:=Subtype.ext (add_smul ..)
lemma spin_b(P Q: Op n): idyl (u+v) (P+Q)= idyl u P+idyl v Q:=by rw [idyl,idyl,idyl,horn_s,show boat (P+Q)=boat P+boat Q from (by apply Subtype.ext; change faceD true false (P+Q)=faceD true false P+faceD true false Q; simp [faceD,twinD,add_smul,sum_add_distrib])]; abel
lemma spin_r(V:ℂ)(P:Op n): Pastry.hollow (Complex.exp V)*exp (boat P)-1 - idyl V P= exp (idyl V P)-1-idyl V P:=by rw [treeL]
variable (F F':E→ℂ)(V V': E→ Op n){Y Y':Toll n}{a b c d:ℝ}
variable (p: Allows k F x a)(h:∀ i j,Allows k (fun y=>V y i j) x (Y i j))(hv:Allows k F' x a)(hq:∀ i j,Allows k (fun y=>V' y i j) x (Y i j))
local notation "S₀"=> fun x=> exp (idyl (F x) (V x))-1
local notation "S₀'"=> fun x=> exp (idyl (F' x) (V' x))-1
local notation "K"=>cull k Y a
local notation "E'"=>saber K
abbrev tide(k:ℕ)(V U:Toll n)(d d':ℝ):=saber (cull k V d) 2 + saber (cull k V d) 2 +cull k U d'
include p h hv hq
lemma evenP (he:Allows k (fun y=> F y+F' y) x b)(hp:∀ i j, Allows k (fun y=> V y i j+ V' y i j) x (Y' i j)): Rigid (fun y=> (S₀) y + (S₀') y) k x (tide k Y Y' a b):=by
 refine (((waxen (opens_g _ _ a Y p h)).addP (waxen (opens_g _ _ a Y hv hq))).addP (opens_g _ (V+V') _ _ he hp)).germ ?_; filter_upwards with y; simp only [Pi.add_apply, spin_b]; -- submodule val
 let Q:= idyl (F y) (V y); let U:= idyl (F' y) (V' y); exact congrArg Subtype.val (by abel : ((exp Q-1-Q)+(exp U-1-U))+(Q+U)=(exp Q-1)+(exp U-1))
end YM.CF.Iva

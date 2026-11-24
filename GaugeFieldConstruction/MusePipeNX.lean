import GaugeFieldConstruction.CartNightNX
import GaugeFieldConstruction.CroatTurn3
import GaugeFieldConstruction.Barrera4
import GaugeFieldConstruction.Photon3
import GaugeFieldConstruction.Sommar
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 100000
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
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
open Ladder3 Drapes Tenant Palot Rue Iona
attribute [local instance] loreM loreN
variable {n: Side}{I α β γ G:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype γ]
-- old bank
namespace ShoreQ
open Tuner
namespace Argos
open XGarden.MastTin
set_option linter.unusedTactic false
open Rio Iona Isle Py Ione Urn Broc Levier Salt
section
open XGarden XGarden.Shield SliceRoof Nacre
variable {n:Side}{d a c t:ℝ}(k:ℕ)(R:Loom n)(F:Elm n Unit d a c)(Y: Orbit n)
variable (μ:ℕ)(o:Seat n)(P:BudgetPoint)(A B:Paper n)(i:L3 n)
variable (K: Support (More n)→ Vox3 n→Cipher n)(D:Force n→ Cipher n)
variable (v:Support (More n))
-- directly linear P field. subtract ζμ.CV.Access.
local notation "Γ"=> AdventureNX F R k t P μ o
abbrev payment3NX (Z:Paper n)(x:L3 n):= AdventureNX F R k t P μ o x Z
lemma Star_μNX :((AdventureNX F R k t P μ o i (A+B)).issue v Y)=(AdventureNX F R k t P μ o i A).issue v Y+(AdventureNX F R k t P μ o i B).issue v Y:=by
 unfold AdventureNX; dsimp only; split_ifs
 · unfold wax; rw [←sum_add_distrib]; apply sum_congr rfl; intro j _; rw [show ∀ j, αLines (A+B) Y.1 j=αLines A Y.1 j+αLines B Y.1 j from (fun j=>rfl),add_smul]
 exact (zero_add _).symm
lemma LifeζNX (y:ℂ): (AdventureNX F R k t P μ o i (y • A)).issue v Y=y • (AdventureNX F R k t P μ o i A).issue v Y:=by
 unfold AdventureNX; dsimp only; split_ifs
 · unfold wax; rw [Finset.smul_sum]; apply sum_congr rfl; intro j _; exact mul_smul ..
 exact (smul_zero _).symm
variable (L:ℕ)(Q:LeaseQ (Support (More n)) n)

section
variable (z:Hub n)(x:Force n)(m:Paper n)(y:ℂ)
local notation "A0" p:max=>payment3NX k R F o P p -- t implicit? need t? shows t implicit cannot infer
-- fix t explicit since def uses t implicit only!
local notation "Ap"=> @payment3NX -- tune
noncomputable def FluteX3NX (Z:Paper n)(t:ℝ): FC (Dwell n):= PortJ Q VoxSpace (fun j:L3 n=> AdventureNX F R k t P μ o j Z) (fun j=>pad3 Q (AdventureNX F R k t P μ o j Z) P L) Y K z
noncomputable def FluteBNX (Z:Paper n)(t:ℝ): FC (Dwell n):= FrontJ Q VoxSpace (fun j:L3 n=>AdventureNX F R k t P μ o j Z) (fun j=>pad3 Q (AdventureNX F R k t P μ o j Z) P L) Y K D x
local notation "G" F:max=> FluteX3NX k R _ Y o P K L Q z F t -- λ $F shadow.
lemma flute_RlNX : FluteX3NX k R F Y μ o P K L Q z (A+B) t =FluteX3NX k R F Y μ o P K L Q z A t+FluteX3NX k R F Y μ o P K L Q z B t:=by
 let q(j):= (Γ j A); unfold FluteX3NX PortJ; rw [← sum_add_distrib]; apply sum_congr rfl; intro j _
 let Z:=AV3 Q (Γ j A)
 let y(p: Z)(A:Paper n):= portR Q VoxSpace Y (Γ j A) (pad3 Q (Γ j A) P L) z (show AV3 Q (Γ j A) from p) K
 change ∑ j: Z,y j _=(∑ j: Z,y j _)+∑ j: Z,y j _; rw [←sum_add_distrib]; apply sum_congr rfl; intro i _
 let W:= pad3 Q (Γ j A) P L i
 let f(w: Heart W VoxSpace i.1.val.2)(A:Paper n):FC (Dwell n):= if z=Legist W VoxSpace i.1.val.2 w then rind (BodyX Q i.1.val.1 i.1.val.2 i.2.val w.val ∅ Y ((AdventureNX F R k t P μ o j A).issue ∅ Y) (K ∅)) else 0 -- tune shadow
-- maybe simply use defeq `change`.
 change ∑ x,f x (A+B)=(∑ x,f x A)+ ∑ x,f x B; rw [←sum_add_distrib]; apply sum_congr rfl;intro w _; unfold f; split; next h=>rw[Star_μNX, advance3,Sault.rind,map_add]
 exact (zero_add _).symm
lemma flute_RsNX : FluteX3NX k R F Y μ o P K L Q z (y • A) t=y • FluteX3NX k R F Y μ o P K L Q z A t:=by
 let q(j):= (Γ j A); unfold FluteX3NX PortJ; rw [Finset.smul_sum]; apply sum_congr rfl; intro j _
 let Z:=AV3 Q (Γ j A)
 let xq(p: Z)(A:Paper n):= portR Q VoxSpace Y (Γ j A) (pad3 Q (Γ j A) P L) z (show AV3 Q (Γ j A) from p) K
 change ∑ j: Z,xq j _=y • (∑ j: Z,xq j _); rw [Finset.smul_sum]; apply sum_congr rfl; intro i _
 let W:= pad3 Q (Γ j A) P L i
 let f(w: Heart W VoxSpace i.1.val.2)(A:Paper n):FC (Dwell n):= if z=Legist W VoxSpace i.1.val.2 w then rind (BodyX Q i.1.val.1 i.1.val.2 i.2.val w.val ∅ Y ((AdventureNX F R k t P μ o j A).issue ∅ Y) (K ∅)) else 0 -- tune shadow
-- maybe simply use defeq `change`.
 change ∑ x,f x _= y • (∑ x,f x A); rw [Finset.smul_sum]; apply sum_congr rfl;intro w _; unfold f; split; next h=>rw[LifeζNX,advanceζ3,Sault.rind,map_smul]
 exact (smul_zero _).symm
lemma flute_BlNX : FluteBNX k R F Y μ o P K D L Q x (A+B) t =FluteBNX k R F Y μ o P K D L Q x A t+FluteBNX k R F Y μ o P K D L Q x B t:=by
 let q(j):= (Γ j A); unfold FluteBNX FrontJ; rw [← sum_add_distrib]; apply sum_congr rfl; intro j _
 let Z:=AV3 Q (Γ j A)
 let y(p: Z)(A:Paper n):= portB_K Q VoxSpace Y (Γ j A) (pad3 Q (Γ j A) P L) x (show AV3 Q (Γ j A) from p) K D
 change ∑ j: Z,y j _=(∑ j: Z,y j _)+∑ j: Z,y j _; rw [←sum_add_distrib]; apply sum_congr rfl; intro i _
 let W:= pad3 Q (Γ j A) P L i
 let f(w:Heart W VoxSpace i.1.val.2)(A:Paper n)(D:Support (More n)):= BodyX Q i.1.val.1 i.1.val.2 i.2.val w.val D Y ((AdventureNX F R k t P μ o j A).issue D Y) (K D)
 let p(w):= Legist W VoxSpace i.1.val.2 w; let r(a:Heart W VoxSpace i.1.val.2)(A:Paper n):= ponyB D (p a) x (f a A)
 change ∑ i,r i (A+B)=(∑ i,r i A)+∑ i,r i B; rw [←sum_add_distrib]; apply sum_congr rfl; intro i _; unfold r; rw[show f i (A+B)=f i A+f i B from (funext (fun S=>by rw[Pi.add_apply]; unfold f; rw[Star_μNX,advance3]))]; unfold ponyB; rw[←sum_add_distrib]; apply sum_congr rfl; intro j _; split; next h=> exact GrantζPlus ..
 exact (zero_add _).symm
lemma flute_BsNX : FluteBNX k R F Y μ o P K D L Q x (y • A) t= y • FluteBNX k R F Y μ o P K D L Q x A t:=by
 let q(j):= (Γ j A); unfold FluteBNX FrontJ; rw [Finset.smul_sum]; apply sum_congr rfl; intro j _
 let Z:=AV3 Q (Γ j A)
 let xq(p: Z)(A:Paper n):= portB_K Q VoxSpace Y (Γ j A) (pad3 Q (Γ j A) P L) x (show AV3 Q (Γ j A) from p) K D
 change ∑ j: Z,xq j _=y • (∑ j: Z,xq j _); rw[Finset.smul_sum]; apply sum_congr rfl; intro i _
 let W:= pad3 Q (Γ j A) P L i
 let f(w:Heart W VoxSpace i.1.val.2)(A:Paper n)(D:Support (More n)):= BodyX Q i.1.val.1 i.1.val.2 i.2.val w.val D Y ((AdventureNX F R k t P μ o j A).issue D Y) (K D)
 let p(w):= Legist W VoxSpace i.1.val.2 w; let r(a:Heart W VoxSpace i.1.val.2)(A:Paper n):= ponyB D (p a) x (f a A)
 change ∑ i,r i _= y • (∑ i,r i A); rw[Finset.smul_sum]; apply sum_congr rfl; intro i _; unfold r; rw[show f i (y • A)= y • f i A from (funext (fun S=>by rw[Pi.smul_apply]; unfold f; rw[LifeζNX,advanceζ3])),pony_scale]
#print axioms flute_BsNX
end
end
end Argos
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end

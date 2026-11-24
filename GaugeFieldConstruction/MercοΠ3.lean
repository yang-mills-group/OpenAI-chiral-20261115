import GaugeFieldConstruction.«Provanκ3»
import GaugeFieldConstruction.Sommar
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 110000
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
variable (P:BudgetPoint)
namespace Argos
section
variable (Q: LeaseQ γ n)(C:Factor3 n)(F: RegLime I α n)(V:Mica I β n)(g:I)
variable {M:Type}[Fintype M](H:M→Support (More n))(r:α→M)(p:∀ j,F.S j=H (r j))
variable (W: Orbit n)(p' d:ℕ)(L:PUnit)(P:Hub n)(R: Fin p'→γ)(x:Key I)
local notation "𝕏"=> FC (Dwell n)
local notation "SD"=> Support (More n)
local notation "Dx"=> Cipher n
-- structural Raw one actor. arbitrary layout Halo.
variable (z:Hub n)(b:Force n)
local notation "U1"=>Heart P H d
local notation "ZV"=> (id:Force n→ Force n)
local notation "MΨ" T:max=> Legist P H d T
variable (A:Support (More n)→FC (Dwell n))(K:Support (More n)→M→Cipher n)(Y: Force n→Cipher n)
def rippleR : FC (Dwell n):=∑ i: Heart P H d, if z=Legist P H d i then rind (BodyX Q p' d R i.val ∅ W (A ∅) (K ∅)) else 0
-- reduce k lane first (force compression independent of Reg)
def ponyB (Y: Force n→ Cipher n)(V:Hub n)(i: Force n)(U:Support (More n)→ FC (Dwell n)) :=∑ j: Base (id:Force n→Force n) V true, if i=roost (id:Force n→Force n) V true j then CGrant U V.val.2 i.val.2 (∏ i∈ j.val,Y i) else 0
local notation "Pψ"=> rippleR Q H W p' d P R z A
local notation "Qp"=> PourUp r
local notation "Vζ"=> fun S=> Qp (fun i=>wax_κ F x W S i)
local notation "Qb"=> PourUp V.z (fun i=> Mu_z V x i W)
local notation "Aχ" S:max=> A S
local notation "ΘΦ" i:max=> if z=(MΨ i) then rind (BodyX Q p' d R i.val ∅ W (A ∅) ((Vζ) ∅)) else 0
def rippleB : FC (Dwell n):=∑ i: Heart P H d, ponyB Y (Legist P H d i) b (fun S=>BodyX Q p' d R i.val S W (A S) (K S))
local notation "ψB"=> Legist P F.S d
include p
lemma ankle : rippleR Q H W p' d P R z A (fun i=> PourUp r (fun j=> wax_κ F x W i j)) = ∑ j: Heart P F.S d, if z=Legist P F.S d j then Sault.rind (BodyX Q p' d R j.val ∅ W (A ∅) (wax_κ F x W ∅)) else 0:=by
 let X(i:Heart P F.S d):= if z=(ψB i) then Sault.rind (BodyX Q p' d R i.val ∅ W (A ∅) (wax_κ F x W ∅)) else 0
 let t:= θRaise H r p P d; change (Pψ Vζ) = ∑ i,X i; rw [sockSum X t]; apply sum_congr rfl; intro i _
 change (if z=Legist P H d i then Sault.rind (BodyX Q p' d R i.val ∅ W (A ∅) ((Vζ) ∅)) else 0)=_; split_ifs with h
 · rw[show BodyX Q p' d R i.val ∅ W (A ∅) (PourUp r (wax_κ F x W ∅))=_ from κpursuit H r p Q P p' d R i ∅ W (wax_κ F x W ∅) (A ∅)]; unfold Sault.rind; rw [map_sum]; apply sum_congr rfl; intro k s; have hu:=mem_filter.mp s; exact (if_pos (show z=Legist P F.S d k from h.trans ((hu.2 ▸ pileR H r p P d k).symm))).symm -- tune
 symm; apply sum_eq_zero; intro k u; have he:t k=i:=(mem_filter.mp u).2; apply if_neg; intro v; exact h (v.trans (he ▸ pileR H r p P d k))
omit p
section pon
variable (Z:Hub n)(q:Force n)(T:Support (More n)→ FC (Dwell n))(a:β→ Cipher n)
lemma hoof_eq : ponyB (PourUp V.z a) Z q T = ∑ k: Base V.z Z true, if q=roost V.z Z true k then CGrant T Z.val.2 (til V.z k.val) (∏ j∈k.val,a j) else 0:=by
 let f(k:Base V.z Z true):= if q=roost V.z Z true k then CGrant T Z.val.2 (til V.z k.val) (∏ j∈k.val,a j) else 0; let P:= φRaise Z V.z true; change ponyB _ Z q T= ∑ j,f j; rw[sockSum f P]; apply sum_congr rfl; intro i _; split_ifs with h
 · rw[press_view, grant_Ax]; apply sum_congr rfl; intro j u; have ho:P j=i:=(mem_filter.mp u).2; have hf:roost V.z Z true j=q:=(riseΖ Z V.z true j).trans (show _=q from (by rw[h,←ho] )) -- tune
   unfold f; rw[if_pos hf.symm,←hf]; rfl
 symm; apply sum_eq_zero;intro j u; have he:P j=i:=(mem_filter.mp u).2; apply if_neg; intro p; apply h; rw [p,←he]; exact riseΖ Z V.z true j
-- maybe after sum_congr
lemma pony_sum (V:Finset M)(p:M→Support (More n)→ FC (Dwell n))(Z:Hub n)(Y:Force n→ Cipher n)(i: Force n): ponyB Y Z i (fun S=>∑ j∈V,p j S)=∑ j∈V,ponyB Y Z i (p j):=by
 unfold ponyB; rw [sum_comm (s:=V)]; apply sum_congr rfl; intro j _; split_ifs
 · rw [grant_AX]
 exact (Finset.sum_const_zero).symm
lemma pony_scale(c:ℂ)(u:Support (More n)→ FC (Dwell n)):ponyB Y z b (c • u)= c • ponyB Y z b u:=by
 unfold ponyB; rw[Finset.smul_sum]; apply sum_congr rfl; intro j _; split_ifs
 · let Z:= ∏ k∈j.val,Y k; have he:=grant_Aτ u z.val.2 b.val.2 Z c 1; rw[one_smul,mul_one] at he; exact he
 exact (smul_zero _).symm
end pon
include p
lemma anta : rippleB Q H W p' d P R b A (fun i=> PourUp r (fun j=> wax_κ F x W i j)) (PourUp V.z (fun i=> Mu_z V x i W))= ∑ j: Heart P F.S d, ∑ k:Base V.z (Legist P F.S d j) true, if b=roost V.z (Legist P F.S d j) true k then CGrant (fun S=>BodyX Q p' d R j.val S W (A S) (wax_κ F x W S)) (Legist P F.S d j).val.2 (til V.z k.val) (∏ i∈k.val,Mu_z V x i W) else 0:=by
 let B:= fun j=> Mu_z V x j W
 unfold rippleB; let Y:= PourUp V.z B
 let a(z:Heart P F.S d)(S:Support (More n)):= BodyX Q p' d R z.val S W (A S) (wax_κ F x W S)
 let t:= θRaise H r p P d; let f(x):= ponyB Y (Legist P F.S d x) b (a x); refine Eq.trans (b:=∑ j,f j) ?_ ?_; swap; · apply sum_congr rfl; intro j _; exact hoof_eq V _ b (a j) B
 rw [sockSum f t]; apply sum_congr rfl; intro i _
 let L0:= univ.filter fun x=> t x=i -- binder
 rw[show (fun S=> BodyX Q p' d R i.val S W (A S) _)=(fun S=>∑ j∈ L0,a j S) from funext fun s=>κpursuit H r p Q P p' d R i s W _ _]; rw [pony_sum]; apply sum_congr rfl; intro j h; have he: i=t j:= (mem_filter.mp h).2.symm
 unfold f; rw[show Legist P F.S d j=Legist P H d (t j) from pileR H r p P d j,he]
end
end Argos
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end

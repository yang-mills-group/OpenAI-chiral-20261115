import GaugeFieldConstruction.«MercοΠ3»
import GaugeFieldConstruction.Sommar
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
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
variable (Q: LeaseQ γ n)(F: RegLime I α n)(V:Mica I β n)(g:I)(σ:I→Seat n)
variable {M:Type}[Fintype M](H:M→Support (More n))(r:α→M)(p:∀ j,F.S j=H (r j))
variable {J:Type}[Fintype J][LinearOrder J](x:Key I)(l:Seat n→J)(b:Bool)(pr:Injective l)
local notation "𝕏"=> FC (Dwell n)
local notation "SD"=> Support (More n)
local notation "Dx"=> Cipher n
variable (S:Ids n)(Y:Orbit n)
def yank (F:RegLime I α n)(r:α→M)(z:Key I)(W: Orbit n):=fun i=>PourUp r (fun j=> wax_κ F z W i j)
def yankB (z:Key I):= PourUp V.z (fun i=> Mu_z V z i Y) -- tune arg order
section
local notation "Fκ"=> Reflect3 σ l b x
local notation "ζz" t:max=> blank3 σ (σ g) (Fκ t)
variable (R: FC (Dwell n)→+ FC (Dwell n))(t:∀ s:ℂ,∀ y:FC (Dwell n),R (s • y)=ρ3 b s • R y)
section
variable {W:Type}(Fz:W)
def ag_top (T:(W→ Cipher n)):FC (Dwell n):= R ((T Fz).val)
abbrev axle_P : (W→ Cipher n) →+ FC (Dwell n):=⟨ ⟨ag_top R Fz, map_zero _⟩,fun i j=>map_add R (i Fz).val (j Fz).val⟩
lemma ax_s (p:∀ s:ℂ,∀ y:FC (Dwell n),R (s • y)=ρ3 b s • R y)(c:ℂ)(y: W→ Cipher n): axle_P R Fz (c • y)= ρ3 b c • axle_P R Fz y:=p c _
end
section
variable (z:Hub n)(y:Force n)(P:Factor3 n)(A: AV3 Q P)(L:Locker Q P)
variable (s:∀ D:Support (More n),Fock.Sector univ false (P.issue D Y))(e:∀ j,P.issue ∅ (Y.1,j)=P.issue ∅ Y)(v:∀ i j,Q.issue i ∅ (Y.1,j)= Q.issue i ∅ Y)(u:∀ i j,F.K i ∅ (Y.1,j)=F.K i ∅ Y)
local notation "aΞ" k:max=> κhop F Q P g V L S k
local notation "ΘX"=> pureT
local notation "R1"=> Rinc σ (κhop F Q P g V L S (A,false))
local notation "H1"=> (symbols_in F Q P g L A)
def portR (z:Hub n)(A:AV3 Q P)(W:SD→ M → Cipher n):=rippleR Q H Y A.1.val.1 A.1.val.2 (L A) A.2.val z (fun S=>P.issue S Y) W -- SD notation macro.M.check
abbrev portB_K (z:Force n)(A:AV3 Q P)(W:Support (More n) → M→ Cipher n)(K: Force n→ Cipher n):=rippleB Q H Y A.1.val.1 A.1.val.2 (L A) A.2.val z (fun S=>P.issue S Y) W K
local notation "N" i:max=> yank F r (ζz i) Y
include v u e p s pr t
lemma profR : Kin (id:J→J) (fun i=>ag_top R Y.1 (Canz σ _ (Rinc σ (κhop F Q P g V L S (A,false))) (Reflect3 σ l b x i) z)) (fun i=> R ((Reflect3 σ l b x i g) • portR Q H Y P L z A (yank F r (blank3 σ (σ g) (Reflect3 σ l b x i)) Y))) :=by
 let p':=A.1.val.1; let d:=A.1.val.2; let H0:= L A; let M' := (H1).pureT V S; let C (X:Support (More n)):= P.issue X Y
 let Q1:= axle_P R Y.1; let L0:=Heart H0 F.S d; let p(x':L0):= Legist H0 F.S d x'; let r0(j:L0)(z':Key I):=BodyX Q p' d A.2.val j.val ∅ Y (C ∅) (wax_κ F z' Y ∅)
 let D(j:L0):= M'.termR j; let E(j:L0):=clipK σ (p j) (g:: tags F d H0 j) (D j)
 have ht(i:Key J): portR Q H Y P L z A (yank F r (ζz i) Y)= ∑ j:L0,if z=p j then rind (r0 j (ζz i)) else 0:= ankle Q F H r ‹∀ j,_› Y p' d H0 A.2.val (ζz i) z C -- tune args
 change Kin id (fun i=> Q1 (Canz σ _ (∑ j:L0,E j) (Reflect3 σ l b x i) z)) _
 simp_rw [ht,can_pour,Finset.sum_apply, Finset.smul_sum,map_sum]; apply loft_bank; intro j _
 let K:= fun i=> (Reflect3 σ l b x i g)*carR (ζz i) (tags F d H0 j); let D0:= D j
 have hz:= clipGear σ l pr x b Q1 (ax_s b R Y.1 t) z (p j) D0 (tags F d H0 j) g
 have hm(i:Key J): Q1 (if z=p j then K i • D0 else 0)= R ((Fκ i g) • (if z=p j then rind (r0 j (ζz i)) else 0)):=by
    split; next b=> unfold K; rw [mul_smul]; change R ((Fκ i g) • ((carR (ζz i) (tags F d H0 j)) • _)) = _
                    have hp:= νpure Q P F V g Y H0 p' d (ζz i) A.2 j ((specs₃ ..).1 A.1.property) s S e v u; exact congrArg (fun x=> R ((Fκ i g) • x)) hp
    rw[map_zero,smul_zero,map_zero]
 simp_rw [←hm]; exact hz
omit v u e
lemma profB : Kin (id:J→J) (fun i=> ag_top R Y (Canz σ _ (Kinc σ (κhop F Q P g V L S (A,true))) (Reflect3 σ l b x i) y)) (fun i=>R ((Reflect3 σ l b x i g) • portB_K Q H Y P L y A (yank F r (blank3 σ (σ g) (Reflect3 σ l b x i)) Y) (yankB V Y (blank3 σ (σ g) (Reflect3 σ l b x i))))) :=by
 let p':= A.1.val.1; let d:=A.1.val.2; let H0:=L A; let M':= (H1).busyT V; let C (X:Support (More n)):=P.issue X Y
 let Q1:=axle_P R Y; let q:= Heart H0 F.S d; let pp(x:q):= Legist H0 F.S d x; let K(j:q):= Base V.z (pp j) true; let D(j:q)(k:Base V.z (pp j) true):= M'.termB j k.val; let Z(j:q):= roost V.z (pp j) true
 let K2(j:q)(i:Base V.z (pp j) true):= tags F d H0 j ++ V.legend i.val
 let E(j:q)(k:Base V.z (pp j) true):= clipK σ (Z j k) (g:: K2 j k) (D j k)
 let O(j:q)(k:Base V.z (pp j) true)(i:Key I):= if y=Z j k then CGrant (fun S=>BodyX Q p' d A.2.val j.val S Y (C S) (wax_κ F i Y S)) (pp j).val.2 (til V.z k.val) (∏ s∈k.val,Mu_z V i s Y) else 0 -- j.val alias risk
 have hx(i:Key I): portB_K Q H Y P L y A (yank F r i Y) (yankB V Y i)=∑ j:Heart H0 F.S d, ∑ k:Base V.z (pp j) true,O j k i:=anta Q F V H r p Y p' d H0 A.2.val i y C
 change Kin id (fun t=> Q1 (Canz σ _ (∑ j:Heart H0 F.S d,∑ k:Base V.z (pp j) true,E j k) (Reflect3 σ l b x t) y)) _
 simp_rw [hx,can_pour,Finset.sum_apply,map_sum,Finset.smul_sum,map_sum]; apply loft_bank; intro j _; apply loft_bank; intro k _
 let H1':=K2 j k; let HV:= Z j k
 have hw(t:Key J):Q1 (if y=HV then (Fκ t g * carR (ζz t) H1') • (D j k) else 0)=R (Fκ t g • O j k (ζz t)):=by
    unfold O; split_ifs <;> try contradiction
    next e=> let P:= νboat Q P F V g Y H0 p' d (ζz t) A.2 j ((specs₃ ..).1 A.1.property) s k.val
             rw [mul_smul]; exact congrArg (fun i=> R (Fκ t g • i)) P
    rw[map_zero,smul_zero,map_zero]
 simp_rw[←hw]; exact clipGear σ l pr x b Q1 (ax_s b R Y t) y (Z j k) (D j k) (K2 j k) g
#print axioms profB
end
end
end Argos
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end

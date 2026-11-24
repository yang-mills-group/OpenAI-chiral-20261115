import GaugeFieldConstruction.MargiaP3
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
variable (Q:LeaseQ γ n)(F: RegLime I α n)(V:Mica I β n)(g:I)(σ:I→Seat n)
variable {M:Type}[Fintype M](H:M→Support (More n))(r:α→M)(p:∀ j,F.S j=H (r j))
variable {J:Type}[Fintype J][LinearOrder J](x:Key I)(l:Seat n→J)(b:Bool)(pr:Injective l)
local notation "𝕏"=> FC (Dwell n)
local notation "SD"=> Support (More n)
local notation "Dx"=> Cipher n
variable (S:Ids n)(Y:Orbit n)
local notation "Fκ"=> Reflect3 σ l b x
local notation "ζz" t:max=> blank3 σ (σ g) (Fκ t)
variable (R: FC (Dwell n)→+ FC (Dwell n))(t:∀ s:ℂ,∀ y:FC (Dwell n),R (s • y)=ρ3 b s • R y)
variable {G:Type}[Fintype G](C:G→Factor3 n)(L:(i:G)→Locker Q (C i))
local notation "N" i:max=> yank F r (ζz i) Y
open Rio
include p
section reef
variable {b0:Bool}{d0:ℕ}(T:Tuner I F.S)
local notation "U" b:max=>Base V.z b
lemma goneB :Kinc σ (pureT V T S)=0:=by
 unfold Kinc; refine sum_eq_zero (fun i _=>sum_eq_zero (fun j _=>?_)); funext k; unfold clipK; split <;> rfl
lemma goneR : Rinc σ (busyT V T)=0:=by
 unfold Rinc; refine sum_eq_zero (fun i _=>?_); funext j; unfold clipK; split <;> try rfl
end reef
omit p
abbrev PortJ (Y:Orbit n)(K:Support (More n)→M→Cipher n)(z:Hub n): FC (Dwell n):=∑ i:G,∑ j:AV3 Q (C i),portR Q H Y (C i) (L i) z j K
abbrev FrontJ (Y:Orbit n)(K:Support (More n)→M→Cipher n)(A:Force n→Cipher n)(i:Force n): FC (Dwell n):=∑ j:G,∑ z:AV3 Q (C j),portB_K Q H Y (C j) (L j) i z K A
local notation "X0"=> purchase3 F Q g V C L S σ
local notation "ΓA"=> Actors Q C
local notation "Z"=> Craft3 F Q g V C L S
lemma beam_s : pureX (purchase3 F Q g V C L S σ)=∑ i:G,∑ j:AV3 Q (C i),Rinc σ (κhop F Q (C i) g V (L i) S (j,false)):=by
 unfold purchase3; rw [κpClip]; unfold Actors; rw [Fintype.sum_sigma]; apply sum_congr rfl; intro i _; rw[Fintype.sum_prod_type]; apply sum_congr rfl; intro j _; rw [Fintype.sum_bool]; rw [show (Rinc σ (Craft3 F Q g V C L S ⟨i,j,true⟩))=0 from ?_,zero_add]; rfl
 exact goneR F V σ (fun i=>F.S i) id (fun _=>rfl) _ -- Args tune
lemma beam_v : (purchase3 F Q g V C L S σ).B=∑ i:G,∑ j:AV3 Q (C i),Kinc σ (κhop F Q (C i) g V (L i) S (j,true)):=by
 change (∑ j:Actors Q C,Kinc σ (Craft3 F Q g V C L S j))= _; unfold Actors; rw [Fintype.sum_sigma]; apply sum_congr rfl; intro i _; rw[Fintype.sum_prod_type]; apply sum_congr rfl; intro j _; rw [Fintype.sum_bool]; rw [show (Kinc σ (Craft3 F Q g V C L S ⟨i,j,false⟩))=0 from ?_,add_zero]; rfl
 exact goneB F V σ (fun i=>F.S i) id (fun _=>rfl) S _
section
variable (u:∀ i:G,∀ D:Support (More n), Sector univ false ((C i).issue D Y))(v:∀ i:G,∀ j,(C i).issue ∅ (Y.1,j)=(C i).issue ∅ Y)(w:∀ i j,Q.issue i ∅ (Y.1,j)=Q.issue i ∅ Y)(h:∀ i j,F.K i ∅ (Y.1,j)=F.K i ∅ Y)
include u v w h p pr t
lemma pennPay3 (z:Hub n) : Kin (id:J→J) (fun i=>ag_top R Y.1 (Canz σ _ (pureX (purchase3 F Q g V C L S σ)) (Reflect3 σ l b x i) z)) (fun i=>R ((Reflect3 σ l b x i g) • PortJ Q H C L Y (yank F r (blank3 σ (σ g) (Reflect3 σ l b x i)) Y) z)):=by
 let Q1:= axle_P R Y.1; change Kin id (fun i=>Q1 (Canz σ _ (pureX (purchase3 F Q g V C L S σ)) _ z)) _; rw [beam_s]; unfold PortJ; simp_rw [can_pour, Finset.sum_apply,Finset.smul_sum,map_sum]; apply loft_bank; intro i _; apply loft_bank; intro j _; exact profR Q F V g σ H r p x l b pr S Y R t z (C i) j (L i) (u i) (v i) w h
lemma pennBeam3 (z:Force n) : Kin (id:J→J) (fun i=>ag_top R Y (Canz σ _ (purchase3 F Q g V C L S σ).B (Reflect3 σ l b x i) z)) (fun i=> R ((Reflect3 σ l b x i g) • FrontJ Q H C L Y (yank F r (blank3 σ (σ g) (Reflect3 σ l b x i)) Y) (yankB V Y (blank3 σ (σ g) (Reflect3 σ l b x i))) z)):=by
 let Q1:=axle_P R Y; change Kin id (fun i=>Q1 (Canz σ _ (purchase3 F Q g V C L S σ).B _ z)) _; rw [beam_v]; unfold FrontJ; simp_rw [can_pour, Finset.sum_apply,Finset.smul_sum,map_sum]; apply loft_bank; intro i _; apply loft_bank; intro j _; exact profB Q F V g σ H r p x l b pr S Y R t z (C i) j (L i) (u i)
#print axioms pennPay3
#print axioms pennBeam3
end
-- domain pin incidence all.pureX & B.
variable (k:I)
lemma actorH3 (i:Actors Q C): KidValid g (Craft3 F Q g V C L S i):=by
 obtain ⟨i,j,b⟩:= i; cases b; exact ⟨fun j=>Or.inl List.mem_cons_self,fun x v=>Or.inr rfl⟩; exact ⟨fun _=>Or.inr (Or.inl rfl),fun i x=>Or.inl List.mem_cons_self⟩ -- tune b_Unit.
lemma pennyOff3 (h:x g=0) : Canz σ _ (pureX (purchase3 F Q g V C L S σ)) x=0 ∧ Canz σ _ (purchase3 F Q g V C L S σ).B x=0:=by unfold purchase3; apply Rio.Kins _ _ _ (actorH3 Q F V g S C L) _ h
end Argos
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end

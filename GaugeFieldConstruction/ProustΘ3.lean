import GaugeFieldConstruction.«AthκP3»
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
variable {n:Side}{α β M N:Type}[Fintype α][Fintype β][Fintype M][Fintype N](V:Sweep n)
section
variable (Q:LeaseQ α n)(H:LeaseQ β n)(g:α ≃ β)
variable (P P': Factor3 n)(h:P.pure=P'.pure)(p:orbit4 V P.H=P'.H)
variable (d:∀ i,H.H (g i)=actY V (Q.H i))(t:∀ i,H.X (g i)=actY V (Q.X i))
variable (u:BudgetPoint)(v:ℕ)
include h p d
lemma shadeG : pts₃ (fadeN P)=pts₃ (fadeN P') :=by rw[fadeN,fadeN,h]
def s_move : BD3 P ≃ BD3 P' where
 toFun i:=⟨i.val, shadeG V Q H g P P' h p d ▸ i.property⟩
 invFun i:=⟨i.val,(by rw [shadeG V Q H g P P' h p d]; exact i.property)⟩
 left_inv _:=rfl
 right_inv _:=rfl
def Actorζ : AV3 Q P ≃ AV3 H P':= Equiv.sigmaCongr (s_move V Q H g P P' h p d) (fun i=> progressL3 V Q.H H.H g P.H P'.H i.val.1 p d)
local notation "Gκ"=> Actorζ V Q H g P P' h p d
local notation "LK"=> pad3 Q P u v
local notation "KV"=> pad3 H P' u v
local notation "XK" i:max=> (Actorζ V Q H g P P' h p d i)
local notation "R0"=> progressL3 V Q.H H.H g P.H P'.H
-- warning Equiv.sigmaCongr toFun casts wrangle.
variable (x:AV3 Q P)
noncomputable def zoom3 (x:AV3 Q P):AV3 H P':= ⟨s_move V Q H g P P' h p d x.1, progressL3 V Q.H H.H g P.H P'.H x.1.val.1 p d x.2⟩
lemma film_e : Actorζ V Q H g P P' h p d x=zoom3 V Q H g P P' h p d x:=by
 rcases x with ⟨x,i⟩; unfold Actorζ zoom3 Equiv.sigmaCongr; simp; rfl -- tune
include t
lemma ramp : orbit4 V (pad3 Q P u v x)=pad3 H P' u v (Actorζ V Q H g P P' h p d x):=by
    rw [film_e]; let m:=zoom3 V Q H g P P' h p d x
    apply Subtype.ext; apply Prod.ext
    · change (orbit4 V _).val.1=P'.H.val.1; exact ((stamp4 V).center _).trans (p ▸ (stamp4 V).center P.H).symm -- tune
    change (orbit4 V _).val.2= (KV m).val.2; rw[z_spec]; change actY V ((if P.pure then ∅ else Lattice.halo _ _) ∪ (core3 Q P x).val.2)=(KV m).val.2 -- tune.v ambiguity
    let U(i:Seat n):=Lattice.halo (ThermalH v*u.B) {i}
    have hc:(core3 H P' m).val.1=(core3 H P' m).val.1:=rfl
    have hp:actY V {P.H.val.1}={P'.H.val.1}:=by rw[←phi_m]; unfold θSet; rw[image_singleton, ←(stamp4 V).center, p]
    rw [show ∀ X Y:Support (More n),actY V (X ∪ Y)=_ from (fun X Y=> (show _=actY V X∪actY V Y from (Finset.map_union ..))),h]
    apply congrArg₂ (·∪·) _ _ -- tune
    · change actY V (if P'.pure then ∅ else U P.H.val.1)= (if P'.pure then ∅ else U P'.H.val.1); split; exact Finset.map_empty _; unfold U; rw[←walkA,hp]
    have he:P'.H.val.2=actY V P.H.val.2:=p ▸ z_spec V P.H
    change actY V (P.H.val.2 ∪ _) = P'.H.val.2∪ univ.biUnion (fun i:Fin x.1.val.1=> H.X (g (x.2.val i))) -- dependent P'.H. C.bar issue rw he
    rw[he, ←phi_m,←phi_m]; unfold θSet; rw [image_union, biUnion_image]; congr 2; funext i; rw[t,←phi_m]
section
variable (Y:M→Support (More n))(X:N→Support (More n))(f:M ≃ N)(e:∀ i,X (f i)=actY V (Y i))
variable (U U': Orbit n)(k:∀ i:α,∀ D:Support (More n),H.issue (g i) (actY V D) U'= suit_Y V (Q.issue i D U))
variable (K:Support (More n)→ M→ Cipher n)(K':Support (More n)→N→Cipher n)(κ:∀ D: Support (More n),∀ i:M,K' (actY V D) (f i)=suit_Y V (K D i))(μ:∀ D:Support (More n),P'.issue (actY V D) U'=lotR3 V (P.issue D U))
variable (G G': Force n→ Cipher n)(w:∀ i,G' (arm4 V i)= suit_Y V (G i))
include e k κ μ
lemma portB3 (z:Hub n): lotR3 V (portR Q Y U P (pad3 Q P u v) z x K)=portR H X U' P' (pad3 H P' u v) (orbit4 V z) (Actorζ V Q H g P P' h p d x) K':=by
 have hp:= ramp V Q H g P P' h p d t u v x; rw[film_e] at hp ⊢
 exact capR V Q H (fun S=>P.issue S U) (fun S=>P'.issue S U') K K' Y X g f U U' _ _ _ _ e k κ μ _ hp z -- tune
include w
lemma port_K3 (z:Force n): lotR3 V (portB_K Q Y U P (pad3 Q P u v) z x K G)=portB_K H X U' P' (pad3 H P' u v) (arm4 V z) (Actorζ V Q H g P P' h p d x) K' G':=by
 have hp:=ramp V Q H g P P' h p d t u v x; rw [film_e] at hp ⊢; exact capB V Q H (fun S=>P.issue S U) (fun S=>P'.issue S U') K K' Y X g f U U' _ _ _ _ e k κ μ G G' w _ hp z
#print axioms portB3
#print axioms port_K3
end
end
end Argos
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end

import GaugeFieldConstruction.«Pintaκ3»
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
variable (P:BudgetPoint)
namespace Argos
open XGarden.MastTin
set_option linter.unusedTactic false
open Rio Iona Isle Py Ione Urn Broc Levier Salt
variable {n:Side}
variable (V:Sweep n)
local notation "φ"=> orbit4 V
local notation "Ω"=> arm4 V
local notation "Φ"=> θSet (boxA V).symm
abbrev flipΘ :Bool:= V.charge.xor (detX V.s)
abbrev lotR3 : FC (Dwell n)→+*FC (Dwell n):= lotY V.charge (detX V.s) (launchZ V)
lemma lot_SC (s:ℂ)(y:FC (Dwell n)):lotR3 V (s • y)= ρ3 (flipΘ V) s • lotR3 V y:=by rw [← sign3]; exact G_lot ..
lemma lot_cipher (x:Cipher n): (suit_Y V x).val=lotR3 V x.val:=rfl -- tune
lemma lot_rind (x:FC (Dwell n)): lotR3 V (rind x)=rind (lotR3 V x):= plower ..
lemma phi_m (Y:Support (More n)): θSet (boxA V).symm Y=actY V Y:= by unfold θSet actY; rw[Finset.map_eq_image]; rfl
lemma z_spec (A:Hub n): (orbit4 V A).val.2=actY V A.val.2:=by rw[←phi_m]; exact (stamp4 V).tile _
lemma joint_m (A B:Support (More n)): Disjoint (actY V A) (actY V B)↔Disjoint A B:=by rw[←phi_m,←phi_m]; exact Same4.d_p ..
lemma unit_m (p:Force n): (arm4 V p).val.2=actY V p.val.2:=by rw[←phi_m]; exact (stamp4 V).band _
-- Force geometry β̂.V. kernel.B.Rota.
section
variable (P Q: Hub n)(b:Bool)
local notation "PX" i:max=>plateI (id:Force n→Force n) i
local notation "Pζ"=> (id:Force n→ Force n)
abbrev tiltX :Equiv.Perm (Finset (Force n)):= Equiv.finsetCongr (arm4 V)
lemma tilt_img(i:Finset (Force n)): tiltX V i=i.image (arm4 V):= Finset.map_eq_image .. -- tune coe via of.
lemma plate3 (i:Force n): plateI (id:Force n→Force n) (arm4 V i)=actY V (plateI id i):=by
 change ((arm4 V i).val.1.val.2)= _; rw[(stamp4 V).pair, z_spec]; rfl
lemma beamw (P:Finset (Force n)) : walls (id:Force n→Force n) (tiltX V P)=actY V (walls (id:Force n→Force n) P):=by
 rw[tilt_img, ←phi_m]; unfold walls θSet; rw [image_biUnion,biUnion_image]; congr 1; funext y; rw[plate3,←phi_m]
lemma rootw (P:Finset (Force n)): til (id:Force n→Force n) (tiltX V P)=actY V (til id P):=by
 rw[tilt_img, ←phi_m]; unfold til θSet; rw[image_biUnion, biUnion_image]; congr 1; funext y; rw[show sealI (id:Force n→Force n) (arm4 V y)= _ from unit_m ..,←phi_m]; rfl
lemma pureBasis (i:Finset (Force n)):BasisI (id:Force n→Force n) P b i ↔ BasisI id (orbit4 V P) b (tiltX V i):=by
 have ht(k r:Force n): Disjoint (PX (Ω k)) (PX (Ω r)) ↔ Disjoint (PX k) (PX r):=by rw[plate3,plate3,joint_m]
 have hd(i:Force n): Disjoint (φ P).val.2 (PX (Ω i)) ↔ Disjoint P.val.2 (PX i):=by rw[plate3,z_spec,joint_m]
 have hv: Disjoint (φ P).val.2 (til id (tiltX V i))↔Disjoint P.val.2 (til Pζ i):=by rw [z_spec,rootw,joint_m]
 rw[tilt_img] at hv ⊢; constructor
 · intro h; refine ⟨?_, ?_,image_nonempty.mpr h.inhab,h.meeting.imp_right (mt hv.mp)⟩
   · intro i v j t p; obtain ⟨a,r,rfl⟩:=mem_image.mp v; obtain ⟨y,f,rfl⟩:=mem_image.mp t; exact (ht a y).2 (h.packed r f (fun z=> p (congrArg _ z)))
   · intro i g; obtain ⟨j,p,rfl⟩:=mem_image.mp g; exact mt (hd j).1 (h.busy _ p)
 intro u; exact ⟨fun i t j p q=> (ht i j).1 (u.packed (mem_image_of_mem _ t) (mem_image_of_mem _ p) ((Ω).injective.ne q)),fun i t h=> u.busy _ (mem_image_of_mem (arm4 V) t) ((hd _).2 h), image_nonempty.mp u.inhab, u.meeting.imp_right (mt hv.mpr)⟩ -- tune
noncomputable def BasisRide(q: orbit4 V P=Q): Base (id:Force n→Force n) P b ≃ Base id Q b:= Equiv.subtypeEquiv (tiltX V) (fun i=> q ▸ pureBasis V P b i)
lemma ride_loc (q: orbit4 V P=Q)(z:Base (id:Force n→Force n) P b) : arm4 V (roost (id:Force n→Force n) P b z)=roost (id:Force n→Force n) Q b (BasisRide V P Q b q z):=by
 apply Subtype.ext; apply Prod.ext
 · change (Ω _).val.1= _; rw[(stamp4 V).pair]; apply Subtype.ext; apply Prod.ext
   · change (φ (mixedHub P Pζ z.val)).val.1=Q.val.1; rw [←q,(stamp4 V).center,(stamp4 V).center]
   change (orbit4 V _).val.2=Q.val.2∪ walls _ (tiltX V z.val); rw[z_spec,beamw,show Q.val.2=_ from q ▸ z_spec V P]; exact Finset.map_union .. -- tune lhs.C.
 change (arm4 V _).val.2=til (id:Force n→Force n) (tiltX V z.val); rw [unit_m,rootw]; rfl
end
-- Heart geometry Reg pairs.E
section he
variable {ι M: Type}[Fintype ι][Fintype M](Y:ι→Support (More n))(X:M→Support (More n))(f:ι ≃ M)(H:Hub n)(G:Hub n)(d:ℕ)(p:orbit4 V H=G)(w: ∀ i,X (f i)=actY V (Y i))
include w p
lemma heartL (x:Fin d→ι):x∈ LeadQ H.val.2 Y d↔ f ∘ x∈LeadQ G.val.2 X d:=by
 have hp(i:ι):f i∈ clouds X G.val.2 ↔ i∈ clouds Y H.val.2:=by simp only [clouds, mem_filter, mem_univ,true_and, show G.val.2=_ from (p ▸ z_spec V H), w,joint_m]
 simp only [LeadQ,mem_filter, mem_univ,true_and,comp_apply,hp]
noncomputable def progressL3 :Heart H Y d ≃ Heart G X d where
 toFun x:=⟨f∘x.val,(heartL V Y X f H G d p w x.val).1 x.property⟩
 invFun x:=⟨f.symm ∘ x.val,(heartL V Y X f H G d p w _).2 (show f ∘ _∈ _ from (by change f ∘ (f.symm ∘ x.val)∈ _; rw [←comp_assoc,Equiv.self_comp_symm]; exact x.property))⟩
 left_inv x:=Subtype.ext (funext fun j=> f.symm_apply_apply _)
 right_inv x:=Subtype.ext (funext fun j=> f.apply_symm_apply _)
lemma innerG (y:Heart H Y d): Legist G X d (progressL3 V Y X f H G d p w y)=orbit4 V (Legist H Y d y):=by
 apply Subtype.ext; apply Prod.ext; exact (show G.val.1=(φ (Legist H Y d y)).val.1 from p ▸ ((stamp4 V).center H).trans (((stamp4 V).center (Legist H Y d y)).symm))
 change G.val.2 ∪(univ.biUnion (fun j=> X (f (y.val j))))=(φ (Legist H Y d y)).val.2
 rw [show G.val.2=actY V H.val.2 from p ▸ z_spec V H,z_spec,←phi_m,←phi_m]; unfold θSet; change _ ∪ _=Finset.image _ (H.val.2 ∪ _); rw[image_union, biUnion_image]; congr 2; funext i; rw[w,←phi_m]; rfl
#print axioms innerG
end he
end Argos
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end

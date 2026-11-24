import GaugeFieldConstruction.Lopeman3
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
open Rill XGarden XGarden.MastTin
open Iona Isle Rio Py Nor Py.Riant
variable (P:BudgetPoint)(σ:I→Seat n) (F: KK I (Copy n) n) (W0: Finset I→Vow.Pax n)(Q0: Finset I→ Vow.Cusp n)
variable (Q:LeaseQ γ n)(L K:ℕ){J:Type}[Fintype J](C:I→J→Factor3 n)(r h a ℓ E Ω η δ u:ℝ)(k j₀:ℕ)
variable (S:Ids n)
section
open Tuner
variable (i:I)(X:XE I (InkD n) n)(A:PI I n) (hN:2*(MastTin.ThermalH L*P.B)< (More n).val) (D:List I)
-- Pure vs Gray for any. pureT $d<=fade and needs>0 means !pure applies. So hi.Term may be false.
local notation "Πopt"=> Book3 P σ F W0 Q0 Q L C S
local notation "Ξ"=> penStep P σ F W0 Q0 Q L C S
lemma somed3 {θ E β₁:Type}[AddCommMonoid E](F:θ→β₁→E)(X:Finset θ)(i:β₁)(w:(∑ x∈X,F x) i ≠0):∃ j∈X,F j i≠0:=by by_contra! h; exact w ((Finset.sum_apply ..).trans (sum_eq_zero h))
include hN
lemma FullWidth (p: (Book3 P σ F W0 Q0 Q L C S D).Y A ≠0):∃ i∈D, ∃ j:J, i∈ A.1 ∧ ((C i j).H.val.1=A.2.val.1 ∧ L < coverNumber P.B A.2.val.2):=by
 induction D using List.reverseRecOn with
 | nil=> exact (p rfl).elim
 | append_singleton l i ih=>
    rw[Book3_cons] at p; let X:= Πopt l; let Y:= Ξ X i
    by_cases h:X.Y A≠0; · obtain ⟨k,t,w⟩:=ih h; exact ⟨k,List.mem_append_left _ t,w⟩
    have hp:Y.Y A≠0:=fun q=>p (show X.Y A+Y.Y A=0 from by rw[Classical.not_not.mp h,q,zero_add])
    let F0 := Craft3 (Frame3 σ W0 Q0 X) Q i (FortX3 F X) (C i) (Platform Q (C i) P L) S
    change (Grotto.gray σ (Craft3 (Frame3 σ W0 Q0 X) _ _ _ _ _ _)) A≠0 at hp
    unfold Grotto.gray at hp; obtain ⟨j,b,h⟩:=somed3 _ _ _ hp; let V:=F0 j; let G':= C i j.1
    have hK:V.needs > 0:=(mem_filter.mp b).2
    unfold Rinc at h; obtain ⟨a,w,t'⟩:=somed3 _ _ _ h; unfold clipK at t'; split at t'
    next hZ=>
       let Z:=Legist V.anchor (Frame3 σ W0 Q0 X).S V.needs a
       have hr: i∈ V.fromR a:=by
          obtain ⟨k,t,u⟩:=j; cases u
          exact List.mem_cons_self
          exact List.mem_cons_self
       have hx: V.needs=j.2.1.1.val.2:=by unfold V F0 Craft3 κhop; split_ifs<;>rfl
       have hu:G'.pure=false:= Bool.eq_false_iff.mpr (fun p=> Nat.not_lt.mpr (le_trans (b:= j.2.1.1.val.1+j.2.1.1.val.2) (hx ▸ Nat.le_add_left ..) (((specs₃ ..).1 j.2.1.1.property).trans_eq (if_pos p))) hK)
       have hy:spark3 Q (C i) P L j= V.anchor:= (placeH ..).symm
       rw[hZ.2]; exact ⟨i,by simp,j.1,List.mem_toFinset.mpr hr,(show (spark3 Q (C i) P L j).val.1= V.anchor.val.1 from congrArg (fun x:Hub n=> x.val.1) hy),lt_of_lt_of_le (point_pad Q _ P _ j.2.1 hu hN) (Corona.cover_mono (show (spark3 Q (C i) P L j).val.2 ⊆ Z.val.2 from (Eq.le (congrArg (fun x:Hub n=>x.val.2) hy)).trans (show V.anchor.val.2⊆ Z.val.2 from subset_union_left)) P.B)⟩
    contradiction
omit hN
lemma muted3 (A:KI I n)(q:(Πopt D).B A ≠0):∃ j∈ D,j∈A.1:=by
    have he(x k i)(x': Heart _ _ _)(y) : k∈ (Craft3 (Frame3 σ W0 Q0 x) Q k (FortX3 F x) (C k) (Platform Q (C k) P L) S i).fromB x' y:=by
       obtain ⟨j,i,f⟩:= i; cases f <;> exact List.mem_cons_self
    induction D using List.reverseRecOn with
    | nil=> exact (q rfl).elim
    | append_singleton l j ih=>
       rw[Book3_cons] at q; let P':= Πopt l; by_cases h:P'.B A=0; swap
       · obtain ⟨i,a,h⟩:=ih h; exact ⟨i,List.mem_append_left _ a,h⟩
       let V:=Ξ P' j; have ht:V.B A≠0:=fun e=>q (show P'.B A+V.B A=0 from by rw[h,e,add_zero]); change (∑ i:Actors Q (C j), Kinc σ (Craft3 (Frame3 σ W0 Q0 P') _ _ _ _ _ _ i)) A≠0 at ht; obtain ⟨i,h,e⟩:=somed3 _ _ _ ht
       unfold Kinc at e; obtain ⟨x,s,w⟩:=somed3 _ _ _ e; obtain ⟨P,k,v⟩:=somed3 _ _ _ w; unfold clipK at v; split at v
       next a=> rw [a.2]; exact ⟨j,List.mem_append_right _ (List.mem_singleton_self _),List.mem_toFinset.mpr (he _ _ _ _ _)⟩
       contradiction
-- pure unit rule.E. audited generically.B cap single.Support. 
lemma plumeL(A:PI I n)(p:(Book3 P σ F W0 Q0 Q L C S D).X A≠0):∃ j∈D,∃ i:Actors Q (C j), i∈ IIW Q (C j)∧ ({j},spark3 Q (C j) P L i)=A:=by
 induction D using List.reverseRecOn with
 | nil=> exact (p rfl).elim
 | append_singleton l j ih=>
    rw[Book3_cons] at p; let X:=Book3 P σ F W0 Q0 Q L C S l; by_cases h:X.X A≠0; · obtain ⟨i,t,x⟩:= ih h; exact ⟨_,by simp[t],x⟩
    let F':= Frame3 σ W0 Q0 X; let V':= FortX3 F X; let Y:= Platform Q (C j) P L; have q:(purchase3 F' Q j V' (C j) Y S σ).X A≠0:=fun q=>p (by change X.X A+(purchase3 F' Q j V' (C j) Y S σ).X A= _; rw[Classical.not_not.mp h,q,add_zero]); unfold Y at q; rw [whiteBill] at q
    obtain ⟨i,t,b⟩:=somed3 _ _ _ q; unfold clipK at b; split at b; next f=> exact ⟨_,by simp,i,t,f.2.symm⟩
    contradiction
-- marker calendar when there is Exactly one pure, always reachable. earlier.T
include hN
variable (Z:I→ J)(hZ:∀ i j,(C i j).pure=true ↔ j=Z i)
variable (hn:D.Nodup)
include hn hZ
lemma pups(s:i∈D)(x:Hub n)(p:coverNumber P.B x.val.2 ≤ L)(R:InkD n)(H: ∀ j:Actors Q (C i), j∈ IIW Q (C i)→j.1=Z i → PoleQ Q (C i) S j=R):pureX (Book3 P σ F W0 Q0 Q L C S D) ({i},x)=if x=(C i (Z i)).H then R else 0:=by
 have hv: (Book3 P σ F W0 Q0 Q L C S D).Y ({i},x)=0:=by by_contra h; obtain ⟨q,t,j,Y,f,T⟩:=FullWidth P σ F W0 Q0 Q L C S ({i},x) hN D h; exact not_lt_of_ge p T
 rw[pureX,Pi.add_apply,hv,add_zero,WhiteMap,←List.sum_toFinset _ hn,Finset.sum_apply, Finset.sum_eq_single_of_mem i (List.mem_toFinset.mpr s) (fun j v δ=> Classical.byContradiction (fun t=>δ (only_α P σ Q L C S j i x t)))]
 let K: Factor3 n:=C i (Z i)
 let T:=K.H; have hp: K.pure=true:= (hZ ..).2 rfl
 let B:BD3 K:= ⟨(0,0),(specs₃ ..).mpr (Nat.zero_le _)⟩
 let P': Actors Q (C i):=⟨Z i,⟨⟨B,⟨Fin.elim0,mem_filter.mpr ⟨mem_univ _,fun i=>Fin.elim0 i⟩⟩⟩,false⟩⟩ -- syntax.P
 have h:P'∈IIW Q (C i):=mem_filter.mpr ⟨mem_univ _,rfl,rfl⟩
 have hg (j:Actors Q (C i))(d:j∈ IIW Q (C i))(f:j.1=Z i) : j=P':=by
    rcases j with ⟨i0,⟨p,b⟩⟩; have he:i0=Z i:= f; subst i0 -- avoid!
    obtain ⟨j,y⟩:=p; have hz:j=B:=by
       apply Subtype.ext; have ht: j.val.1+j.val.2≤ fadeN K:= (specs₃ ..).1 j.property; have hc:= ht.trans_eq (show fadeN K=0 from if_pos hp)
       refine Prod.ext ?_ ?_ <;> dsimp only [B] <;> omega -- tune using B.val
    subst j; -- Unique y. use.
    have h:b=false:=(mem_filter.mp d).2.2
    refine Sigma.ext (Eq.refl (Z i)) ?_
    rw[h]; refine heq_of_eq ?_; change ((⟨B,y⟩,_):AV3 Q K × Bool)=_; letI:IsEmpty (Fin B.val.1):=inferInstanceAs (IsEmpty (Fin 0)); congr; exact Subsingleton.elim (α:=↥(LeadQ _ _ B.val.1)) _ _
 have hz:spark3 Q (C i) P L P'=K.H:=pure_pad Q K P L _ hp
 unfold airs_r; rw[Finset.sum_apply,Finset.sum_eq_single_of_mem P' h, clipK]
 swap; · intro j t g; unfold clipK; split; next w=>
           have hT:x=spark3 Q (C i) P L j:=congrArg Prod.snd w.2; by_cases y: j.1=Z i; exact False.elim (g (hg j t y)); exact (not_lt_of_ge p (by rw [hT]; exact point_pad Q _ _ _ _ (Bool.eq_false_iff.mpr (mt (hZ _ _).1 y)) hN)).elim
         rfl
 rw [hz,H P' h rfl]
 change (if ψS σ [i]∧ _ then _ else _)=_; simp only [ψS,List.map_singleton,List.nodup_singleton,true_and, show [i].toFinset={i} from (by simp),Prod.mk.injEq,true_and]; rfl -- tune
#print axioms pups
end
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end

import GaugeFieldConstruction.MolFloP3
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
open Rio Iona Isle
variable (Q: LeaseQ γ n)(F: RegLime I α n)(V:Mica I β n)(g:I)(σ:I→Seat n)
variable {M:Type}[Fintype M](H:M→Support (More n))(r:α→M)(p:∀ j,F.S j=H (r j))
local notation "𝕏"=> FC (Dwell n)
local notation "SD"=> Support (More n)
local notation "Dx"=> Cipher n
section
open Py Py.Riant
variable (P: BudgetPoint)(K:KK I (Copy n) n)(W0:Finset I→Pax n) (Q0:Finset I→Cusp n)(X:Rio I n)(z:Key I)(Y:Orbit n)(S:Ids n)
abbrev Vox3(n:Side):= Aura n⊕ Hub n
abbrev VoxSpace: Vox3 n→ Support (More n):= Sum.elim (fun x=>x.val) (fun i=> i.val.2)
noncomputable def VoxPos (v:Tψ I n): Vox3 n:=v.elim (fun i=>Sum.inl i.2) (fun i=>Sum.inr i.2)
lemma legV (j:Tψ I n):(Frame3 σ W0 Q0 X).S j= VoxSpace (VoxPos j):=by rcases j with z|z <;> rfl
abbrev DropW (Y:Orbit n)(P:Pax n)(Q:Cusp n)(H:RegBudget n):Support (More n) → Vox3 n→ Cipher n :=fun D=> Sum.elim (fun j=> if Disjoint D j.val then P j Y else -(Q j (D∩j.val) Y)) (fun j=>if Disjoint D j.val.2 then H j Y.1 else 0)
variable (vW:∀ i∈realm_C σ, Bake.Turf (W0 i))
local notation "ZP"=> Frame3 σ W0 Q0 X
local notation "KF"=> FortX3 K X
include vW
lemma turf3 (i:Tψ I n)(T:Ids n): (Frame3 σ W0 Q0 X).K i ∅ (Y.1,T)=(Frame3 σ W0 Q0 X).K i ∅ Y:=by
 rcases i with ⟨J,L⟩ | ⟨J,L⟩
 · change ((if _ then _ else 0):Copy n) _=((if _ then _ else 0):Copy n) _; split; next g=> rw[if_pos (Finset.disjoint_empty_left L.val)]; exact vW _ g ..
   rfl
 change ((if Disjoint (∅:Support (More n)) L.val.2 then oV (pureX X (J,L)) else 0):Copy n) _=((if Disjoint (∅:Support (More n)) L.val.2 then oV (pureX X (J,L)) else 0):Copy n) _; split <;> rfl
omit vW
section rep
variable {M E:Type}[Fintype M][DecidableEq M][CommRing E][Module ℂ E]
lemma termScope (F:dues I M→E)(v:∀ i:dues I M, F i≠0→i.1∈realm_C σ) : PourUp Prod.snd (fun i=> carR z (Cue I i.1) • F i)= Canz σ E F z:=by
 funext i; unfold PourUp Canz; rw [sum_filter,Fintype.sum_prod_type] -- ambiguous predicate? inferred α=M
 let f(t:Finset I):=∑ j:M, if j=i then carR z (Cue I t) • F (t,j) else 0; change ∑ j:Finset I,f j=_
 have h(p:Finset I):f p=Mew.pine p z • F (p,i):=by unfold f; rw[sum_eq_single i, if_pos rfl,sorterH]; intro j _ q; rw[if_neg q]; simp
 simp_rw[h]; symm; refine sum_subset (subset_univ _) (fun j k p=>?_) -- arguments braces
 rw [show F (j,i)=0 from Classical.byContradiction (fun u=>p (v _ u)), smul_zero]
end rep
variable (v:∀ i:PI I n,pureX X i≠0 → i.1∈realm_C σ)
variable (u:∀ i:KI I n,K i≠0→ i.1∈realm_C σ)(w:∀ i:KI I n,X.B i≠0→ i.1∈realm_C σ)
include v
lemma vox_P : yank (Frame3 σ W0 Q0 X) VoxPos z Y=DropW Y (WritV σ W0 z) (WritV σ Q0 z) (Canz σ _ (pureX X) z):=by
 funext i h; unfold yank PourUp wax_κ Frame3 Tψ; rw [sum_filter,Fintype.sum_sum_type]; rcases h with j | j; -- tune DecidableEq.N.F.M.K
 · rw [sum_eq_zero (s:=(univ:Finset (PI I n))), add_zero]; swap; · intros i k; simp[VoxPos] -- erase
   let k:=realm_C σ; let t(i₁:Finset I)(j':Aura n):= if j=j' then Mew.pine i₁ z • (past σ W0 Q0).K (i₁,j') i Y else 0
   unfold WA3 dues; rw[Fintype.sum_prod_type]; let P(t:Finset I):=t -- tune
   let f(i₁:Finset I)(j':Aura n):= if VoxPos (Sum.inl (i₁,j'):Tψ I n)=Sum.inl j then carR z (Cue I i₁) • (past σ W0 Q0).K (i₁,j') i Y else 0
   refine Eq.trans (b:=∑ i₁:Finset I,∑ x:Aura n,f i₁ x) ?_ ?_
   · refine sum_congr rfl (fun i _=>sum_congr rfl (fun k _=>?_)); unfold f; split_ifs <;> rfl
   have hv(l:Finset I): ∑ j', f l j'= Mew.pine l z • (past σ W0 Q0).K (l,j) i Y:=by
      rw [sum_eq_single j]; unfold f; rw[if_pos (show VoxPos (Sum.inl ((l,j):WA3 I n))=Sum.inl j from rfl), sorterH]; intro x _ h; unfold f; exact if_neg (fun p=> h (Sum.inl.inj p)); simp -- f h typo
   simp_rw[hv]; let g(l: Finset I):= Mew.pine l z • (past σ W0 Q0).K (l,j) i Y
   have hp:∑ j':Finset I,g j'= ∑ j'∈realm_C σ,g j':=(sum_subset (subset_univ _) (fun j _ q=>by unfold g past; dsimp only; rw[if_neg q,Pi.zero_apply,smul_zero])).symm
   change ∑ j', g j'= if Disjoint i j.val then _ else _; rw[hp]; unfold WritV; simp_rw [Finset.sum_apply, Pi.smul_apply]; split
   next m=> exact sum_congr rfl (fun p t=>by unfold g past; dsimp only; rw[if_pos t, if_pos m])
   next m=> rw[←Finset.sum_neg_distrib]; apply sum_congr rfl; intro p t; unfold g past; dsimp only; rw[if_pos t, if_neg m, Pi.neg_apply, smul_neg]
 rw [sum_eq_zero (s:=(univ:Finset (WA3 I n))), zero_add]; swap; · intros i k; simp [VoxPos]
 unfold DropW; dsimp only [Sum.elim_inr]; split
 next e=> let F:= pureX X
          rw [←termScope σ z F v,PourUp,Finset.sum_apply,sum_filter]; apply sum_congr rfl; intro u _
          split; next h=> have ht:u.2=j:=Sum.inr.inj h; rw[if_pos ht]
                          change carR z (Cue I u.1) • ((if Disjoint i u.2.val.2 then oV (pureX X u) else 0):Copy n) Y=_; rw[if_pos (show Disjoint _ _ from (show Disjoint i u.2.val.2 from (by rw[ht]; exact e)))]; rfl
          next h=> rw[if_neg (show u.2≠j from fun k=> h (show VoxPos (Sum.inr u)=_ from congrArg Sum.inr k))]
 next x=> apply sum_eq_zero; intro u _; split; next p=>
           have ht:u.2=j:=Sum.inr.inj p; change carR z _ • ((if Disjoint i u.2.val.2 then _ else 0):Copy n) Y= _; rw [if_neg (show ¬Disjoint i u.2.val.2 from (by rw[ht]; exact x)), Pi.zero_apply,smul_zero]
          rfl
omit v
include u w
lemma vox_B : yankB (FortX3 K X) Y z = (fun i=> Canz σ _ (K+X.B) z i Y):=by
 have hp:∀ i:KI I n,(K+X.B) i ≠0→ i.1∈realm_C σ:= by
   intro i t; by_cases p:K i=0; · exact w i (by rwa[Pi.add_apply,p,zero_add] at t)
   exact u i p
 rw [←termScope σ z _ hp]; funext i; unfold yankB PourUp; rw [Finset.sum_apply]; rfl
#print axioms vox_P
end
end Argos
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end

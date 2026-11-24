import GaugeFieldConstruction.Vigor3
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
open Iona Isle Rio Py Nor Py.Riant -- tune
variable (P:BudgetPoint)(W:Orbit n)(σ:I→Seat n)(z:Key I)
local notation "D0"=> Aura n
local notation "Ω"=> flags P.threshold W.1
-- table creds old.Q
structure Entrance3 (σ:I→Seat n)(E:RegLime I α n) (K:Mica I β n)(X Υ:Key I→ RegBudget n)(Y:Key I→ ForceBudget n)(P:BudgetPoint): Prop where
    lens(W:Orbit n)(u:Rue.FleetS P.threshold W.1) : River (fun z=>exponentL P (X z) W.1)
    back(W:Orbit n)(u:Rue.FleetS P.threshold W.1) : ∃ c:Key I→ℂ,(∀ z, exponentL P (X z) W.1=c z • (1:Cipher n) + ∑ j:α, φU E P W z j)
    mask_g(W: Orbit n)(u:Rue.FleetS P.threshold W.1):∀ z, PourUp K.z (fun i=>Tuner.Mu_z K z i W)=fun i=>Y z i W
-- past.DenZ overlay. defEq Prop.Stencils.
section
variable (F:KK I (Copy n) n) (W0: Finset I→Vow.Pax n)(Q0: Finset I→ Vow.Cusp n)(U0:RegBudget n)(A:XE I (InkD n) n)(X:Rio I n)
abbrev WA3(I:Type)(n:Side):= dues I (Aura n)
abbrev Tψ(I:Type)(n:Side):=(WA3 I n)⊕PI I n
-- old W and Q group single choice. Q charged **plus** W.L.P.PostCombined..
local notation "ω"=> extraD
abbrev pastMask : WA3 I n → Support (More n) :=fun i=> i.2.val
def past : RegLime I (WA3 I n) n:=⟨fun i=> i.2.val,(fun i=>Cue I i.1),fun i X=> if i.1∈realm_C σ then (if Disjoint X i.2.val then W0 i.1 i.2 else -Q0 i.1 i.2 (X∩i.2.val)) else 0⟩ -- disjoint symmetric
local notation "Pz"=> past σ W0 Q0
lemma τpast (v: FleetS P.threshold W.1): ∑ j: WA3 I n,φU (Pz) P W z j=coldE P (WritV σ W0 z) W - fuelV P (WritV σ Q0 z) W :=by
 let Λ:=realm_C σ; unfold WA3 dues coldE fuelV
 simp_rw [WritV, Finset.sum_apply,Pi.smul_apply]; rw[sum_filter,sum_filter,Fintype.sum_prod_type,sum_comm, ←sum_sub_distrib]; apply sum_congr rfl; intro i h
 let Y:=i.val; have hp(k:Finset I): φU Pz P W z (k,i) = if k∈realm_C σ then if Disjoint Ω i.val then (pine k z) • (W0 k i W) else -(pine k z • Q0 k i (Ω∩ i.val) W) else 0:=by
    unfold φU past; dsimp only; split_ifs with hj hj' -- tune
    rw [sorterH] -- tune
    rw [sorterH]; exact smul_neg ..
    exact smul_zero _
 by_cases v': Disjoint Ω i.val
 · have hx: pingS _ i.val W.1:= (shoreK _ _ v _).1 v'.symm
   simp_rw[hp, if_pos v']; rw[if_pos hx,if_neg (show ¬fuelH Ω i from fun u=>u (v'.symm)),sub_zero,←sum_filter]; -- tune order fuelH
   rw [Finset.filter_mem_eq_inter,Finset.univ_inter]
 have hm:¬ pingS P.threshold i.val W.1:=fun x=>v' ((shoreK _ _ v _).2 x).symm; simp_rw [hp,if_neg v']; rw [if_neg hm,if_pos (show fuelH Ω i from ?_), zero_sub,←sum_filter,Finset.sum_neg_distrib]
 rw [Finset.filter_mem_eq_inter,Finset.univ_inter]
 exact fun q=>v' q.symm
local notation "M" i=> cloudP i
abbrev ripeFrame (V:XE I (InkD n) n) : RegLime I (PI I n) n:=⟨fun i=> i.2.val.2, fun i=>Cue I i.1,fun i D=> if Disjoint D i.2.val.2 then oV (V i) else 0 ⟩
abbrev mergeP(A:RegLime I α n)(B:RegLime I γ n): RegLime I (α⊕γ) n:=⟨Sum.elim A.S B.S, Sum.elim A.V B.V, Sum.elim A.K B.K⟩
def Frame3 : RegLime I (Tψ I n) n := mergeP (past σ W0 Q0) (ripeFrame (pureX X))
def FortX3 (K: KK I (Copy n) n)(W:Rio I n): Mica I (KI I n) n:=⟨Prod.snd, fun x=>Cue I x.1,K+W.B⟩
section
variable (h r:ℝ)(U Y:WA3 I n→ℝ)(V:PI I n→ℝ)(E:XE I (InkD n) n)(ΨP:BillX P σ h r V E)
structure Plen_E : Prop where
    loyW : Ledges (SecW P (h:=0) le_rfl n) σ W0 -- doesn't need h
    loyQ : Ledges (SecQ P 0 n) σ (fun i=>FlatQ (Q0 i))
    sitesW(i:WA3 I n)(e:i.1∈realm_C σ) :Medal P i.2.val ∅ (W0 i.1 i.2) h (Bplain i.1.card (U i) r)
    sitesQ (i:WA3 I n)(e:i.1∈realm_C σ)(D: Support (More n))(t:D.Nonempty)(v:D⊆ i.2.val): Medal P i.2.val D (Q0 i.1 i.2 D) h (Bplain i.1.card (Y i) r)
    turf(i:Finset I)(p:i∈realm_C σ): Bake.Turf (W0 i)
variable (p:Plen_E P σ W0 Q0 h r U Y) (s:0<r) (u:0≤ U)(w:0≤ Y)
include p s u w
lemma legacy_Q : RegPay (past σ W0 Q0) P σ r h (U+Y):=by
 constructor
 · rintro ⟨i,j⟩ D; let A:= (U+Y) (i,j); have ht:0≤ A:= add_nonneg (u _) (w _)
   change Medal P j.val (j.val∩D) (if _ then _ else 0) h (Bplain (Cue I i).length A r); rw [show (Cue I i).length=i.card from length_sort ..]; split
   next g=> split
            next u' => rw [Finset.disjoint_iff_inter_eq_empty.mp u'.symm]; exact (p.sitesW (i,j) g).big (div_le_div_of_nonneg_right (le_add_of_nonneg_right (show 0≤Y _ from w _)) (pow_pos s _|>.le))
            next hk=> have he:(D∩j.val).Nonempty:=by rw[←Finset.not_disjoint_iff_nonempty_inter]; exact hk
                      rw [inter_comm j.val]; refine (p.sitesQ (i,j) g _ he inter_subset_right |>.negT).big (div_le_div_of_nonneg_right (le_add_of_nonneg_left (show 0≤ U _ from u _)) (pow_pos s _|>.le))
   next ht'=>exact Medal.zeroT.big (div_nonneg ht (pow_pos s _|>.le))
 · rintro ⟨i,j⟩ D v; change poke_F _ j.val ((Cue I i).toFinset); rw [show (Cue I i).toFinset=i from sort_toFinset ..]
   unfold past at v; dsimp only at v; split at v
   next y=>
     split at v; next h=>
       obtain ⟨u,v⟩:=Function.ne_iff.mp v; exact (p.loyW _ u trivial i v).2 -- tune
     next h=>
       obtain ⟨u,v⟩:=Function.ne_iff.mp v; exact (p.loyQ j (D∩j.val,u) (show ΘV _ _ from ⟨not_disjoint_iff_nonempty_inter.mp h, inter_subset_right⟩) i (fun p=> v (show -(_)=0 from (by change -(Q0 _ _ _ _)=0; change Q0 _ _ _ _=0 at p; rw[p,neg_zero])))).2
   contradiction
 · intro i D X u; change i.2.val ∩D=i.2.val ∩X at u; unfold past; dsimp only; split <;> try rfl
   rw[inter_comm i.2.val D,inter_comm i.2.val X] at u; simp_rw [disjoint_iff_inter_eq_empty,u]
 intro i x T; unfold past; dsimp only; split; next g=> rw [if_pos (Finset.disjoint_empty_left _)]; exact p.turf i.1 g ..
 rfl
omit p u w
include ΨP
lemma planΞ : RegPay (ripeFrame E) P σ r h V:=by
 constructor
 · intro i D; have hp:0≤ V i:= ΨP.gist i; change Medal P _ _ (ite _ _ _) h (Bplain (Cue I i.1).length (V i) r); split; next v=> rw [disjoint_iff_inter_eq_empty.mp v.symm, show (Cue I i.1).length=i.1.card from length_sort ..]; exact ΨP.lit _
   exact Medal.big Medal.zeroT (div_nonneg hp (pow_pos s _|>.le))
 · intro i D h; change ite _ (_:Copy n) _≠0 at h; split at h; next g=>
     change poke_F _ _ ((Cue I i.1).toFinset); rw [show (Cue I _).toFinset=i.1 from sort_toFinset ..]; exact (ΨP.pin _ (fun y=>h (by rw[y]; rfl))).2
   contradiction
 · intro i D X h; unfold ripeFrame; change (if _ then _ else _)=if _ then _ else _; change i.2.val.2∩D=i.2.val.2∩X at h; simp_rw [Finset.disjoint_iff_inter_eq_empty,inter_comm D,inter_comm X,h]
 intro i U Q; simp only [ripeFrame, Finset.disjoint_empty_left, if_true]
include ΨP
lemma χ_ripe (v:FleetS P.threshold W.1): ∑ u:PI I n,φU (ripeFrame E) P W z u=exponentL P (Canz σ _ E z) W.1:=by
 let B:= FrameT E (0:KK I (Copy n) n); rw [Γ_formula σ E (0:KK I (Copy n) n) P h r V ΨP W v z] -- tune
 apply sum_congr rfl; intro i _; let Y:=i.2.val.2; unfold φU; change carR z (Cue _ _) • ((if Disjoint Ω i.2.val.2 then _ else 0):Copy n) W=(if Disjoint i.2.val.2 Ω then _ else 0); simp only [show Disjoint Ω i.2.val.2 ↔ _ from (show Disjoint _ _ ↔ Disjoint i.2.val.2 Ω from disjoint_comm)]; split; rfl; exact smul_zero _
end
end
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end

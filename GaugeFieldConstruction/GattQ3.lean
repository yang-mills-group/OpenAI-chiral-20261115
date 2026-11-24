import GaugeFieldConstruction.Vigor3
import GaugeFieldConstruction.Epis
import GaugeFieldConstruction.Tellur
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
open Tenant Branch XGarden XGarden.MastTin
variable (Q:LeaseQ γ n)(C:Factor3 n)
section
-- enlarged Core support. Touch t with Q.H.Wave.
local notation "κ"=> AV3 Q C
def core3 (s:AV3 Q C): Hub n:= let Y:= C.H; ⟨⟨Y.val.1,Y.val.2∪(univ.biUnion fun j:Fin s.1.val.1=> Q.X (s.2.val j))⟩,mem_union_left _ Y.property⟩
-- PAD only !pure. Full Halo from its anchor not subject data.
def pad3 (P:BudgetPoint)(L:ℕ)(s:AV3 Q C):Hub n:= let X:=core3 Q C s; ⟨⟨X.val.1,(if C.pure then ∅ else Lattice.halo (ThermalH L*P.B) {X.val.1}) ∪ X.val.2⟩,mem_union_right _ X.property⟩
variable (P:BudgetPoint)(L:ℕ)(s:AV3 Q C)
local notation "G" i:max=> core3 Q C i
local notation "T" i:max=> pad3 Q C P L i
local notation "Θ"=> ThermalH L
local notation "Z"=> (ThermalH L*P.B)
lemma later_p(y:Fin s.1.val.1): Q.X (s.2.val y)⊆(G s).val.2:=fun _ v=>mem_union_right _ (mem_biUnion.mpr ⟨y,mem_univ _,v⟩)
lemma padd_on:Padd Q C (pad3 Q C P L):=⟨(fun i=>⟨subset_union_left.trans subset_union_right,fun j=>(later_p Q C i j).trans subset_union_right⟩),fun _=>rfl⟩
lemma pad_cover : (T s).val.2⊆ Lattice.halo (Θ*P.B) (G s).val.2:=by
 intro i h; rcases mem_union.mp h with v|v; swap; · exact Lattice.halo_subset _ _ v
 split at v; contradiction; exact Corona.halo_mono le_rfl (singleton_subset_iff.mpr (G s).property) v
lemma halo_pad (h: C.pure=false): Lattice.halo (Θ*P.B) {C.H.val.1}⊆ (T s).val.2:=by unfold pad3; simp only [h,Bool.false_eq_true,↓reduceIte]; exact Finset.subset_union_left
lemma point_pad (h: C.pure=false)(hp:2*(ThermalH L*P.B)<(More n).val) : L<coverNumber P.B (T s).val.2:= by
 have ht:= ThickP L P C.H.val.1 hp; refine lt_of_lt_of_le ht (Corona.cover_mono ?_ P.B); intro i p; apply halo_pad Q C P L s h; obtain ⟨d,t,rfl⟩:= mem_image.mp p
 exact halo_spec.mpr ⟨_,mem_singleton_self _, ((ηspace Z C.H.val.1 d hp).le.trans (by cases d <;> simp only [Option.elim_none,Nat.zero_le,Option.elim_some,le_refl]))⟩
lemma pure_pad (h:C.pure=true): T s=C.H:=by
 apply Subtype.ext; refine Prod.ext rfl ?_; unfold pad3; change (if _ then _ else _) ∪ (G s).val.2=C.H.val.2; rw [if_pos h, Finset.empty_union]
 have hp:= ((specs₃ ..).1 s.1.property).trans_eq (show fadeN C=0 from if_pos h)
 letI:IsEmpty (Fin s.1.val.1):=by rw [show s.1.val.1=0 from (by omega)]; infer_instance
 change C.H.val.2∪ Finset.biUnion _ _= _; rw [Finset.univ_eq_empty,Finset.biUnion_empty,Finset.union_empty]
def SumCone (m:ℕ):ℝ:= (m:ℝ)
section
open Lattice.Corona
lemma grow_v3 (h:Grove (terr _) C.H.val.2)(u:∀ j:Fin s.1.val.1,Grove (terr _) (Q.X (s.2.val j)))(w:∀ j:Fin s.1.val.1,Q.H (s.2.val j)⊆Q.X (s.2.val j)) : Grove (terr _) (G s).val.2:=by
 let X:=C.H.val.2
 have hx(i:Fin s.1.val.1): ¬ Disjoint X (Q.X (s.2.val i)):=fun v=> (mem_filter.mp ((mem_filter.mp s.2.property).2 i)).2 (Disjoint.mono_right (w _) v)
 apply (show ∀ S:Finset (Fin s.1.val.1), Grove (terr _) (X∪ (S.biUnion fun i=>Q.X (s.2.val i))) from ?_)
 intro V; induction V using Finset.induction_on with
 | empty=> simpa using h
 | insert i v p ih=> obtain ⟨j,a,t⟩:=not_disjoint_iff.mp (hx i); rw [biUnion_insert,union_comm (Q.X _), ←union_assoc]; exact ih.unite (u _) (mem_union_left _ a) t
lemma pad_near (h:Grove (terr _) (core3 Q C s).val.2) (t:(core3 Q C s).val.2.card≤P.B): (T s).val.2⊆ Lattice.halo (Θ*P.B) {C.H.val.1}:=by
 intro i v; rcases mem_union.mp v with v|v; · split at v; contradiction; exact v
 have he:separation C.H.val.1 i < (G s).val.2.card:=h.lim _ (G s).property _ v
 apply halo_spec.mpr ⟨_,mem_singleton_self _,he.le.trans (t.trans ?_)⟩; unfold ThermalH; nlinarith
lemma crust (m:ℕ){n:Side}(b:ℕ)(p:0 < b) (a d:ℝ)(t:0≤a)(v:a*2*Yaw.χ m ≤ (b:ℝ)*d)(g:0 ≤ d)(U V:Support n)(u:Grove (terr _) V)(w:U⊆ Lattice.halo (m*b) V): March b a U≤Real.exp (a*Yaw.χ m)* Branch.rent d V:=by
 let X:= Dial.idrat n
 have hv : X.parent=id:=funext fun i =>(show X.parent i=i from (by nth_rw 1 [←Dial.glass i]; exact Ratio.embed_parent ..))
 have he:V.image X.parent=V:=by rw [hv,Finset.image_id]
 have hu:= Yaw.aidV X u (le_refl (m*b)) p t v g; rw [he] at hu
 exact (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (cover_mono w _)) t)).trans hu
#print axioms pad_near
end
end
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end

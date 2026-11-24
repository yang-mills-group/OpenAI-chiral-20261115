import GaugeFieldConstruction.Iroko
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
section port
variable {n:Side}{α:Type*}[Fintype α](z:α→Force n)(P:Scree.Hub n)
variable (w:Bool) -- WantsD (if true always force). False → remote flag in base.
local notation "Y"=>P.val.2
variable (S:Support (More n))(A B:Finset α)
def ashC (P:Hub n)(z:α→Force n)(A:Finset α):= A.filter fun i=> ¬ Disjoint P.val.2 (plateI z i)
abbrev mixedHub (P:Hub n)(z:α→Force n)(C:Finset α): Hub n:=⟨⟨P.val.1,P.val.2∪walls z C⟩, mem_union_left _ P.property⟩
-- tags not necessarily inject. Want over all such covers
structure BasisI (A:Finset α): Prop where
 packed : (A:Set α).Pairwise fun a b=> Disjoint (plateI z a) (plateI z b)
 busy :∀ i∈ A,¬ Disjoint Y (plateI z i)
 inhab:A.Nonempty
 meeting: w = true ∨ ¬Disjoint Y (til z A)
namespace BasisI
local notation "Κ"=> BasisI z P w
variable {z P w A B S}
lemma distinct (h:BasisI z P w A): PriceI z (til z A) A:= ⟨h.packed,rfl⟩
abbrev Base (z:α→Force n)(P:Hub n)(w:Bool):= {A:Finset α//BasisI z P w A}
def roost (z:α→Force n)(P:Hub n)(w:Bool)(A: Base z P w):Force n:=⟨⟨mixedHub P z A.val,til z A.val⟩,⟨by
 obtain ⟨i,h⟩:=A.property.inhab; obtain ⟨x,t⟩:=(z i).property.1; exact ⟨_, mem_biUnion.mpr ⟨i,h,t⟩⟩,fun x p=> by obtain ⟨b,t,h⟩:= mem_biUnion.mp p; exact mem_union_right _ (mem_biUnion.mpr ⟨b,t,(z b).property.2 h⟩)⟩⟩
def Combo (z:α→Force n)(P:Hub n)(w:Bool):α ⊕ Base z P w→Force n:=Sum.elim z (roost z P w)
def Charcoal (g:Hub n)(w:Bool)(S:Support (More n)):Prop:= w=true∨¬Disjoint g.val.2 S
local notation "Z"=> Combo z P w
lemma claimA {C:Base z P w}(h:PriceI (Combo z P w) S (A.disjSum {C})): Charcoal P w S:=by
 rcases C.property.meeting with h0|h0; · exact Or.inl h0
 apply Or.inr; intro t; refine h0 (disjoint_of_subset_right ?_ t); intro i p; rw[←h.covers]; exact mem_biUnion.mpr ⟨.inr C, inr_mem_disjSum.mpr (mem_singleton_self ..),p⟩
lemma til_le {x:Finset α}(h:PriceI z S A)(p:x⊆A):til z x⊆ S:=by rw [← h.covers]; intro i t; obtain ⟨j,e,d⟩:=mem_biUnion.mp t; exact mem_biUnion.mpr ⟨j,p e,d⟩
lemma creek_in (h:PriceI z S A)(B:Finset α)(p:B⊆ A): walls z B∩S=til z B:=by
 ext x; constructor
 · intro t; obtain ⟨w,q⟩:=mem_inter.mp t; obtain ⟨i,g,v⟩:=mem_biUnion.mp w
   exact mem_biUnion.mpr ⟨i,g,(h.foot z (p g)) ▸ (mem_inter.mpr ⟨v,q⟩)⟩
 intro t; obtain ⟨i,k,x'⟩:=mem_biUnion.mp t; exact mem_inter.mpr ⟨mem_biUnion.mpr ⟨i,k,(z i).property.2 x'⟩, til_le h p t⟩
lemma ash_mem {i:α}: i∈ashC P z A ↔ i∈A∧¬Disjoint P.val.2 (plateI z i):=Finset.mem_filter
-- classify any compound exactly recovered by rest/ash decomposition
lemma mixed_spec {C:Base z P w}: PriceI (Combo z P w) S (A.disjSum {C}) ↔ PriceI z S (A∪ C.val) ∧ Disjoint A C.val∧ ashC P z (A∪ C.val)= C.val :=by
 have he: til (Combo z P w) (A.disjSum {C})= til z (A ∪ C.val):=by
    ext x; unfold til; simp_rw [mem_biUnion]; constructor
    · rintro ⟨a,p,q⟩; cases a with
      | inl i=> exact ⟨i,mem_union_left _ (inl_mem_disjSum.mp p),q⟩
      | inr i=> have hh:i=C:=mem_singleton.mp (inr_mem_disjSum.mp p); subst i; obtain ⟨j,a,b⟩:= mem_biUnion.mp (show x∈til z C.val from q); exact ⟨j,mem_union_right _ a,b⟩
    rintro ⟨i,k,h⟩; rcases mem_union.mp k with w|w
    · exact ⟨Sum.inl _,inl_mem_disjSum.mpr w,h⟩
    exact ⟨.inr C,inr_mem_disjSum.mpr (mem_singleton_self ..),show x∈til z C.val from mem_biUnion.mpr ⟨i,w,h⟩⟩
 constructor
 · intro h
   have hx(i:α)(p:i∈A):Disjoint (plateI z i) (P.val.2 ∪ walls z C.val):= h.zone (inl_mem_disjSum.mpr p) (inr_mem_disjSum.mpr (mem_singleton_self ..)) Sum.inl_ne_inr
   have hx'(i k)(p:i∈A)(g:k∈C.val):Disjoint (plateI z i) (plateI z k):=disjoint_of_subset_right (fun v w=>mem_union_right _ (mem_biUnion.mpr ⟨k,g,w⟩)) (hx i p)
   refine ⟨⟨fun x p y q t=>?_,he.symm.trans h.covers⟩,Finset.disjoint_left.mpr (fun {i} p g=> ?_),?_⟩
   · rcases mem_union.mp p with p|p<;>rcases mem_union.mp q with q|q
     · exact h.zone (inl_mem_disjSum.mpr p) (inl_mem_disjSum.mpr q) (fun e=>t (Sum.inl.inj e))
     · exact hx' x y p q
     · exact (hx' y x q p).symm
     exact C.property.packed p q t
   · exact C.property.busy i g (disjoint_of_subset_left Finset.subset_union_left (hx i p).symm)
   ext i; rw[ash_mem,Finset.mem_union]; constructor
   · rintro ⟨p|p,t⟩; · exact False.elim (t (disjoint_of_subset_left subset_union_left (hx i p).symm))
     exact p
   intro g; exact ⟨Or.inr g,C.property.busy _ g⟩
 rintro ⟨h,d,g⟩
 have hx(i:α)(p:i∈A):Disjoint (plateI z i) (P.val.2 ∪ walls z C.val):=by
    have hp: Disjoint P.val.2 (plateI z i):=by
       by_contra v; exact Finset.disjoint_left.mp d p (g ▸ (ash_mem.mpr ⟨mem_union_left _ p,v⟩))
    apply Finset.disjoint_left.mpr; intro k x y; rcases mem_union.mp y with y|y
    · exact Finset.disjoint_left.mp hp y x
    obtain ⟨e,t,v⟩:= mem_biUnion.mp y
    have hm:i≠e:=by rintro rfl; exact Finset.disjoint_left.mp d p t
    exact Finset.disjoint_left.mp (h.zone (mem_union_left _ p) (mem_union_right _ t) hm) x v
 refine ⟨?_,he.trans h.covers⟩; intro a l b s e; cases a with
 | inl x=>
    cases b with
    | inl y=> exact h.zone (mem_union_left _ (inl_mem_disjSum.mp l)) (mem_union_left _ (inl_mem_disjSum.mp s)) (fun k=>e (congrArg Sum.inl k))
    | inr y=> have hl:y=C:= mem_singleton.mp (inr_mem_disjSum.mp s); rw[hl]; exact hx x (inl_mem_disjSum.mp l)
 | inr x=>
    have hl:x=C:=mem_singleton.mp (inr_mem_disjSum.mp l)
    cases b with
    | inl y=> rw [hl]; exact (hx y (inl_mem_disjSum.mp s)).symm
    | inr y=> exact False.elim (e (congrArg Sum.inr (hl.trans (mem_singleton.mp (inr_mem_disjSum.mp s)).symm)))
lemma coast_C (h:PriceI z S A)(c:Charcoal P w S)(p:(ashC P z A).Nonempty) : BasisI z P w (ashC P z A):=by
 let X:=ashC P z A
 refine ⟨fun a t b e=>h.zone ((ash_mem.mp t).1) ((ash_mem.mp e).1),fun i v=>(ash_mem.mp v).2,p,?_⟩
 rcases c with c|c; · exact Or.inl c
 apply Or.inr; intro F
 obtain ⟨x,u,v⟩:=Finset.not_disjoint_iff.mp c; obtain ⟨i,k,hx⟩:=mem_biUnion.mp (show x∈til z A from h.covers ▸ v)
 have hw:i∈X:=ash_mem.mpr ⟨k,fun d=>Finset.disjoint_left.mp d u ((z i).property.2 hx)⟩
 exact Finset.disjoint_left.mp F u (mem_biUnion.mpr ⟨i,hw,hx⟩)
end BasisI
end port
end YM.CF.Scree.Ing
end

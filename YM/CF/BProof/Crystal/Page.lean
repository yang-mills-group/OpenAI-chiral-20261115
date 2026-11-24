import YM.CF.BProof.Crystal.Volume
import YM.CF.Gas.League
/-! Local site graph & Yard. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Crystal
open Function Filter Fock Finset NormedSpace Garden Align Wick Double Pastry Sprinkle Lattice Tenant Palot Gas Branch Stilo
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {V I: Type}[DecidableEq V][Fintype V][Fintype I][LinearOrder I]{P:Dew V I}
-- true alphabet supports micro counties
structure Civic(N:Side)(P:Dew V I) where
 home:I→Site N
 zone: V→Y N
 belt (i): ∀ j∈P.crisp i, home j∈(zone i).val
 peace (i j:V)(h:Disjoint (zone i).val (zone j).val): P.free i j
variable {N:Side}
abbrev Deco(P:Dew V I)(N:Side):= P.Box (Support N)
abbrev Prism(I:Type)(N:Side):= Option (I×Support N)
def prism(S:Prism I N): Support N:= S.elim ∅ fun i=>i.2
namespace Civic
variable (p:Civic N P)
def skin (i: Deco P N): Support N:= univ.biUnion (fun a:P.Slots i.1=>prism (i.2 a))
def border(i: Deco P N):Y N:=⟨(p.zone i.1).val ∪ skin i, (p.zone i.1).property.mono subset_union_left⟩
variable {A: V→ℂ}{F:I→I→Support N→ℂ}
def room (S:Support N) :Finset I:=univ.filter fun i=> p.home i∈ S
def Code (F:I→I→Support N→ℂ):Prop:=∀ i j S, i<j→ F i j S ≠0 → p.home i∈S ∧ p.home j∈S
lemma costume {X: Support N}{S:Finset (Deco P N)} (h:p.Code F)(f:∀ i∈S,P.litmus A F i≠0)(g:S.biUnion (fun i=>(p.border i).val)⊆X): Sector (p.room X) false (P.light S).val:=by
 have hv(i)(hi:i∈S): Sector (p.room X) false (P.flareL i).val:=by
    unfold Dew.flareL; have hx:=right_ne_zero_of_mul (f i hi); have he(j:P.Slots i.1): Sector (p.room X) false (Dew.shine j.val (i.2 j)).val:=by
       cases H:i.2 j with
       | none=> exact Sector.one
       | some K=>
          have ht:Dew.charge F j.val (some K)≠0:=fun k=>hx (prod_eq_zero (mem_univ j) (by rw [H]; exact k)); unfold Dew.charge at ht; rw [Option.elim_some] at ht; by_cases k:j.val<K.1; swap; rw [if_neg k] at ht; contradiction
          obtain ⟨y,z⟩:=h _ _ _ k (fun d=> ht (by rw [if_pos k,d])); let T:=fun (i:Deco P N)=>(p.border i).val; have hm:K.2⊆X:= Subset.trans (s₂:=T i) (fun x w=> mem_union_right _ (mem_biUnion.mpr ⟨j,mem_univ _, H.symm ▸ w⟩)) ((subset_biUnion_of_mem (u:=T) hi).trans g); exact ((Sector.up (S:=p.room X) j.val (mem_filter.mpr ⟨mem_univ _,hm y⟩)).mul (Sector.up (S:=p.room X) K.1 (mem_filter.mpr ⟨mem_univ _,hm z⟩)))
    generalize (univ:Finset (P.Slots i.1))=Y; induction Y using Finset.induction_on with| empty=> rw [prod_empty]; exact Sector.one | insert x Y k IH=> rw [prod_insert k]; exact (he x).mul IH
 unfold Dew.light; induction S using Finset.induction_on with
 | empty=> rw [prod_empty]; exact Sector.one
 | insert i S k ih=> rw [prod_insert k]; refine (hv i (mem_insert_self ..)).mul (ih (fun j e=> f _ (mem_insert_of_mem e)) ?_ (fun x e=> hv _ (mem_insert_of_mem e))); rw [biUnion_insert] at g; exact (union_subset_iff.mp g).2
lemma styleB(S:Finset (Deco P N))(X:Support N)(g:S.biUnion (fun i=>(p.border i).val)⊆X): Sector (p.room X) false (P.beam (down S)).val:=by
 refine Garden.scope (P.beamAt _) ?_; intro i hi; obtain ⟨j,a,b⟩:=mem_biUnion.mp hi; obtain ⟨x,d,rfl⟩:=mem_image.mp a; exact mem_filter.mpr ⟨mem_univ _,g (mem_biUnion.mpr ⟨x,d, mem_union_left _ (p.belt _ _ b)⟩)⟩
lemma roof {S:Finset (Deco P N)}(i: Deco P N)(h:i∈S): (p.zone i.1).val ⊆ (S.biUnion fun i => (p.border i).val) :=fun _ d=> mem_biUnion.mpr ⟨i,h, mem_union_left _ d⟩ -- remove X
-- union linkage tests. duplicate alpha/share
variable {S T:Finset (Deco P N)}(d: Disjoint (S.biUnion (fun i=>(p.border i).val)) (T.biUnion (fun i=>(p.border i).val)))
include d
lemma downPeace {i j:V}(h:i∈down S)(g:j∈down T):Disjoint (p.zone i).val (p.zone j).val:=by obtain ⟨x,u,rfl⟩:=mem_image.mp h; obtain ⟨y,k,rfl⟩:=mem_image.mp g; exact d.mono (p.roof _ u) (p.roof y k)
lemma downDis : Disjoint (down S) (down T):=by rw [Finset.disjoint_left]; intro a h k; apply (p.zone a).property.ne_empty; exact disjoint_self.mp (p.downPeace d h k)
lemma smooth (s:Smooth S)(t:Smooth T): Smooth (S∪T):=by
 intro i hi j hj e; rcases mem_union.mp hi with i|i <;> rcases mem_union.mp hj with j|j
 · exact s i j e
 · exact False.elim (disjoint_left.mp (p.downDis d) (mem_image_of_mem _ i) (e.symm ▸ mem_image_of_mem _ j)) -- tune
 · exact False.elim (disjoint_left.mp (p.downDis d) (mem_image_of_mem _ j) (e ▸ mem_image_of_mem _ i))
 exact t i j e
lemma vicinity (s:P.Honest S)(t:P.Honest T): P.Honest (S∪T):=by
 constructor <;> (intro i hi j hj e; rw [down,image_union] at hi hj; rcases mem_union.mp hi with h|h <;> rcases mem_union.mp hj with g|g)
 · exact s.1 h g e
 · exact p.peace _ _ (p.downPeace d h g)
 · exact p.peace _ _ (p.downPeace d g h).symm
 · exact t.1 h g e
 all_goals try first| exact s.2 h g e | exact t.2 h g e
 · exact disjoint_left.mpr (fun _ x y=> disjoint_left.mp (p.downPeace d h g) (p.belt _ _ x) (p.belt _ _ y))
 exact disjoint_left.mpr (fun _ x y=> disjoint_left.mp (p.downPeace d g h) (p.belt _ _ y) (p.belt _ _ x))
end Civic
end YM.CF.BProof.Crystal

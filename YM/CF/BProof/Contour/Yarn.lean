import YM.CF.BProof.Contour.Ratio

/- regrouping by overlap. complex. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Contour
open Function Filter Moment Finset Relation Push.AbsoluteSums
open scoped Topology BigOperators Classical
variable {B I:Type*}[Fintype B][DecidableEq B][Fintype I][DecidableEq I]
variable (S:I→Finset B)
structure Yarn(F:Finset I→ℂ) : Prop where
 start : F ∅=1
 prod (P Q:Finset I) : Disjoint (hull S P) (hull S Q) → Disjoint P Q→ F (P∪ Q)=F P*F Q
abbrev Toy := {P:Finset I // Spark S P}
def toTrain(P:Finset I): Finset (Toy S):= univ.filter fun i=> i.val∈ Parts S P
def floorT(P:Finset (Toy S)):= P.biUnion Subtype.val
def roofT(x:Toy S):= hull S x.val
lemma outT(P:Finset (Toy S)): (P.image Subtype.val).biUnion id=floorT S P:=by ext x; simp only [Finset.mem_biUnion, Finset.mem_image,id_eq,exists_exists_and_eq_and,floorT]
lemma ebb(P:Finset I) : (toTrain S P).image Subtype.val=Parts S P:=by
 ext i; rw [mem_image]; exact ⟨fun ⟨g,p,t⟩=> t ▸ (mem_filter.mp p).2,fun p=>⟨⟨i,(lives S P p).2⟩,mem_filter.mpr ⟨mem_univ _,p⟩,rfl⟩⟩
lemma ebb_flow(P:Finset I): floorT S (toTrain S P)=P:=by rw [←outT,ebb,reconstruct]
lemma creek(P:Finset I): flock (roofT S) (toTrain S P):= fun i p j q e=> separate S P ((mem_filter.mp p).2) ((mem_filter.mp q).2) (fun t=> e (Subtype.ext t))
lemma pact(P:Finset (Toy S))(p:flock (roofT S) P): toTrain S (floorT S P)=P:=by
 apply map_injective (Function.Embedding.subtype _); simp_rw [map_eq_image]; change Finset.image Subtype.val (toTrain S _)=Finset.image _ _ -- tune
 rw [ebb,← outT]; apply separates; intro i h; obtain ⟨x,h,rfl⟩:=mem_image.mp h; exact x.property
 intro i h j g e; obtain ⟨x,hx,rfl⟩:=mem_image.mp h; obtain ⟨y,gy,rfl⟩:=mem_image.mp g; exact p (show x∈ P from hx) (show y∈ P from gy) (fun w=> e (congrArg Subtype.val w)) -- tune shadow
variable(H:∀ i:I,(S i).Nonempty)
include H
lemma hull_nonempty (i:Toy S): (roofT S i).Nonempty:=by obtain ⟨x,h⟩:=i.property.1; exact (H x).mono (hull_sub S _ _ h)
lemma no_repeat {P Q:Finset I}(p: Disjoint (hull S P) (hull S Q)) : Disjoint P Q:=by
 refine disjoint_left.mpr (fun i h k=>?_); obtain ⟨x,g⟩:=H i; exact disjoint_left.mp p (hull_sub S P i h g) (hull_sub S Q i k g)
variable (F: Finset I→ℂ)(p:Yarn S F)
include p
lemma loft (P:Finset (Toy S))(g:flock (roofT S) P): F (floorT S P)=∏ i∈P,F i.val:=by
 induction P using Finset.induction_on with
 | empty=> simpa [floorT,p.start]
 | insert x T h ih=>
   obtain ⟨g,e⟩:= (shrinkF _ x h).1 g; have hv: Disjoint (hull S x.val) (hull S (floorT S T)):=by apply Disjoint.mono_right ?_ g; intro j p; obtain ⟨i,q,l⟩:= mem_biUnion.mp p; obtain ⟨k,v,f⟩:= mem_biUnion.mp q; exact mem_biUnion.mpr ⟨k,v,hull_sub S k.val i f l⟩ -- tune implicit args
   rw [floorT,biUnion_insert,prod_insert h]; change F (x.val ∪ floorT S T)=_; rw [p.prod _ _ hv (no_repeat _ H hv), ← ih e]
lemma yard_score : ∑ j:Finset I,F j=sumGas (roofT S) (fun x=>F x.val) univ:=by
 symm; apply Finset.sum_nbij' (floorT S) (toTrain S); intro i h; exact mem_univ _; intro i _; exact mem_filter.mpr ⟨mem_univ _, subset_univ _,creek S i⟩
 exact fun i h=>pact S i (mem_filter.mp h).2.2; exact fun i _=>ebb_flow S i; exact fun i h=> (loft S H F p i (mem_filter.mp h).2.2).symm
lemma linked(u:I→ℝ)(g:Toll S u 4 (1/2))(t:∀ i:Finset I,‖F i‖≤ wage u i): Real.exp (-(Fintype.card B:ℝ)) ≤ ‖∑ i:Finset I,F i‖:=by
 rw [yard_score S H F p]; apply held (u:= (payC S u) ∘ Subtype.val); swap; · intro i; unfold Function.comp payC; rw [if_pos i.property]; exact t i.val
 swap; · exact hull_nonempty S H
 let X:=hull S; have ht:= counts S (a:=1) g (by norm_num) zero_le_one; refine ⟨fun i=>ht.nonneg _,fun i=>?_⟩; exact budget_pull Subtype.val Subtype.val_injective (ht.pays i)
end YM.CF.BProof.Contour

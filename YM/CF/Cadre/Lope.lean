import YM.CF.Palot.Pal
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Cadre
open Function Filter Topology Lattice Finset Palot
open scoped Classical
variable {A:Type*}[Fintype A][DecidableEq A]
local notation "ΣA"=> Palot.leaf A
local notation "ΣG"=> hook A
variable (Y:Palot.leaf A)(D O:Finset A)(F:hook A)
-- P supports meeting kernel leaf Y
abbrev stream(D: Finset A): Finset (Finset ΣA):= univ.filter fun G=> flow A G ∧ D ⊆ robe G
abbrev weather (X Y:ΣA)(G:ΣG):Prop:= (∀ j∈G,¬ Disjoint Y.val j.val)∧X.val=Y.val∪robe G
abbrev drum (X Y:ΣA)(D:Finset A): Finset (Finset ΣA):=(stream D).filter fun G=> weather X Y G
def grab (Y:ΣA)(F:ΣG):=F.filter fun i=>¬ Disjoint Y.val i.val
abbrev farR(Y:ΣA)(F:ΣG):= F\grab Y F
def glueV (Y:ΣA)(G:ΣG):ΣA:=⟨Y.val∪ robe G,Y.property.mono subset_union_left⟩
lemma cog {a:ΣA}: a∈grab Y F ↔ a∈F ∧¬Disjoint Y.val a.val:=mem_filter
lemma pact(a:ΣA):a∈farR Y F↔a∈F∧ Disjoint Y.val a.val:=by rw [show (a∈farR Y F)↔a∈F∧a∉grab Y F from mem_sdiff,cog]; tauto
lemma coneL{a:ΣA}{G:ΣG}(h:a∈G):a.val⊆robe G:=subset_biUnion_of_mem Subtype.val h
lemma race :grab Y F ∪ farR Y F=F:= union_sdiff_of_subset (filter_subset ..)
lemma wax:{Q T:ΣG}→ Disjoint (robe Q) (robe T)→Disjoint Q T:=by intro Q T p; refine Finset.disjoint_left.mpr fun {i} j k=>?_ ; obtain ⟨x,h⟩:=i.property; exact Finset.disjoint_left.mp p (coneL j h) (coneL k h)
lemma firm{P Q:ΣG}(p:flow A (P∪Q))(g:Disjoint P Q): Disjoint (robe P) (robe Q):=by
 refine Finset.disjoint_left.mpr fun {i} j k=>?_; obtain ⟨a,t,v⟩:=mem_biUnion.mp j; obtain ⟨w,h,l⟩:=mem_biUnion.mp k; exact Finset.disjoint_left.mp (p _ (mem_union_left _ t) _ (mem_union_right _ h) (fun u=>Finset.disjoint_left.mp g t (u.symm ▸ h))) v l
lemma spire{P Q:ΣG}(p:flow A P)(h:flow A Q)(g:Disjoint (robe P) (robe Q)):flow A (P∪Q):=by
 intro i t j w v; rcases mem_union.mp t with k|k<;> rcases mem_union.mp w with l|l; exact p i k j l v; exact Disjoint.mono (coneL k) (coneL l) g; exact Disjoint.mono (coneL k) (coneL l) g.symm; exact h i k j l v
lemma stilt {P:ΣG}{a:ΣA}(p:flow A P)(g:Disjoint a.val (robe P)) :flow A (insert a P):=by
 rw [←singleton_union]; exact spire (by intro _ p _ t; rw [mem_singleton.mp p,mem_singleton.mp t]; simp) p (by simpa [robe] using g : Disjoint (robe {a}) (robe P))
lemma drum_p {X Y:ΣA}{P:ΣG}: P∈drum X Y D↔ (flow A P ∧ D⊆robe P)∧ (∀ j∈P,¬ Disjoint Y.val j.val)∧ X.val=Y.val∪ robe P:=by rw [drum,mem_filter]; unfold stream; rw [mem_filter,and_iff_right (mem_univ P)]
lemma drive (h:F∈stream D) : let G:=grab Y F; let T:=farR Y F; let X:=glueV Y G
 G∈drum X Y (D∩X.val)∧insert X T∈ stream D ∧ X∉T:=by
 intro G T X; have he:G∪T=F:=race Y F; obtain ⟨p,w⟩:=(mem_filter.mp h).2
 have hp:Disjoint (robe G) (robe T):=firm (he.symm ▸ p) disjoint_sdiff
 have hx:Disjoint X.val (robe T):=Finset.disjoint_union_left.mpr ⟨(by refine Finset.disjoint_left.mpr fun {i} k l=>?_ ; obtain ⟨x,t,v⟩:=mem_biUnion.mp l; exact Finset.disjoint_left.mp ((pact Y F _).mp t).2 k v), hp⟩
 have ha:T⊆F:= subset_union_right.trans (subset_of_eq he)
 have hk:robe G ∪robe T=robe F:=by rw [←he]; unfold robe; rw [union_biUnion]
 refine ⟨(drum_p ..).mpr ⟨⟨flow_m p (filter_subset ..),?_⟩,fun _ h=> ((cog Y F).mp h).2,rfl⟩,mem_filter.mpr ⟨mem_univ _,stilt (flow_m p ha) hx,?_⟩,fun i=>?_⟩ -- tune Q
 · rintro i v; obtain ⟨s,t⟩:=mem_inter.mp v; exact (mem_union.mp (hk.symm ▸ w s)).resolve_right (Finset.disjoint_left.mp hx t)
 · intro i s; rw [robe,biUnion_insert]; rcases mem_union.mp (hk.symm ▸ w s) with u|u; exact mem_union_left _ (subset_union_right u); exact mem_union_right _ u
 obtain ⟨a,s⟩:= X.property; exact Finset.disjoint_left.mp hx s (coneL i s)
lemma sideR (E:ΣG)(e:E∈stream O)(X:ΣA)(t:X∈E)(p:ΣG)(g:p∈drum X Y (O∩X.val)):
 let H:=E.erase X; let G:=p∪H
 G∈ stream O∧ grab Y G=p∧ glueV Y p=X ∧ farR Y G=H:=by
 intro H G; obtain ⟨⟨k,l⟩,a,v⟩:=(drum_p ..).mp g; obtain ⟨u,w⟩:=(mem_filter.mp e).2; have he:E=insert X H:=(insert_erase t).symm
 have hf:H⊆E:=erase_subset _ _; have hx:Disjoint X.val (robe H):=flow_d (he ▸ u) (notMem_erase _ _); have hv:p∪H=G:=rfl
 have hP:Disjoint (robe p) (robe H):=Disjoint.mono_left (v.symm ▸ subset_union_right) hx
 have ht:grab Y G=p:=by
    ext i; constructor
    · intro s; obtain l|l:=mem_union.mp (show i∈p∪H from ((cog Y G).mp s).1); exact l; exact False.elim (((cog Y _).mp s).2 (Disjoint.mono (v.symm ▸ subset_union_left) (coneL l) hx))
    intro h; exact (cog Y _).mpr ⟨mem_union_left _ h,a _ h⟩
 refine ⟨mem_filter.mpr ⟨mem_univ _, spire k (flow_m u hf) hP, ?_⟩,ht,Subtype.ext v.symm,?_⟩
 · intro i r; have hl:= w r; rw [he,robe,biUnion_insert] at hl; unfold G; rw [robe,union_biUnion]; exact mem_union.mpr ((mem_union.mp hl).imp_left fun w=>l (mem_inter.mpr ⟨r,w⟩))
 unfold farR; rw [ht]; exact Finset.ext fun i=> (by rw [show (i∈G\p)↔i∈G∧i∉p from mem_sdiff,←hv,show (i∈p∪H)↔_ from (mem_union: i∈(p∪H:ΣG)↔i∈p∨i∈H)]; constructor; rintro ⟨v,s⟩; exact v.resolve_left s; intro s; exact ⟨Or.inr s,Finset.disjoint_right.mp (wax hP) s⟩)
end YM.CF.Cadre

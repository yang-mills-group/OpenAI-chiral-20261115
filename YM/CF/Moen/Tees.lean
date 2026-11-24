import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Moen
open Function Filter Set Finset Topology
open scoped Classical BigOperators
-- primitive dominating sets with dummy corners. elementary Scarf counting Inspired by common no-bullying idea.
variable {I α β A: Type*}[Fintype I][DecidableEq I][DecidableEq α][DecidableEq β]
section fiber
variable {f:α→β}{S:Finset α}{T:Finset β}
lemma bear (h:S.image f=T)(t:S.card=T.card+1): ∃ i∈ S,∃ j∈ S, i≠j∧ f i=f j∧ Set.InjOn f (S.erase i) ∧ Set.InjOn f (S.erase j):=by
 have hx:¬ Set.InjOn f S:=fun p=>by have he:=Finset.card_image_iff.mpr p; rw [h] at he; omega
 simp only [Set.InjOn] at hx; push_neg at hx; obtain ⟨i,a,j,b,c,u⟩:=hx
 have hr(i j:α)(p:i∈ S)(r:j∈ S)(t':i≠j)(g:f i=f j):Set.InjOn f (S.erase i):=by
    have hv:(S.erase i).image f=T:=Finset.Subset.antisymm (h ▸ image_subset_image (erase_subset ..)) fun x w=>by
       rw [←h] at w; obtain ⟨y,l,m⟩:=mem_image.mp w; by_cases q:y=i; exact mem_image.mpr ⟨j,mem_erase.mpr ⟨t'.symm,r⟩,g.symm.trans (q ▸ m)⟩; exact mem_image.mpr ⟨y,mem_erase.mpr ⟨q,l⟩,m⟩
    apply card_image_iff.mp; rw [hv,card_erase_of_mem p]; omega
 exact ⟨i,a,j,b,u,c,hr i j a b u c,hr j i b a u.symm c.symm⟩
lemma bear_w {i j:α}(u:S.image f=T)(h:S.card=T.card+1)(w:i∈S)(v:j∈S)(he:i≠j)(hq:f i=f j)(p:Set.InjOn f (S.erase i))(e: Set.InjOn f (S.erase j))(k l:α)(x:k∈S)(y:l∈ S)(z:k≠l)(g:f k=f l): k=i ∧ l=j ∨ k=j ∧l=i:=by
 by_cases a:k=i
 · refine Or.inl ⟨a,?_⟩; suffices h:k=l ∨ l=j by tauto
   by_contra m; push_neg at m; exact z (e (mem_erase.mpr ⟨a.symm ▸ he,x⟩) (mem_erase.mpr ⟨m.2,y⟩) g)
 by_cases c:l=i
 · refine Or.inr ⟨?_,c⟩; by_contra V; exact z (e (mem_erase.mpr ⟨V,x⟩) (mem_erase.mpr ⟨c.symm ▸ he,y⟩) g)
 exact False.elim (z (p (mem_erase.mpr ⟨a,x⟩) (mem_erase.mpr ⟨c,y⟩) g))
end fiber
open Finset
variable {R: Type*} [LinearOrder R] [DecidableEq A][Fintype A]
structure Gift(I A R: Type*) [LinearOrder R] where
 corner : I↪ A
 score:I→A→R
 inj(i:I): Function.Injective (score i)
 low(i:I)(x:A):x≠corner i→score i (corner i)<score i x
 high(i j:I): i≠j→∀ x, x ∉ Set.range corner →score i x < score i (corner j)
namespace Gift
variable (G:Gift I A R)(c:I){X Y:Finset A}
local notation "N"=> Fintype.card I
local notation "Ux"=> G.score
local notation "J"=> G.corner
abbrev good(X:Finset A):Prop:=∀ p:A,∃ i:I,∀ j∈ X,Ux i p ≤ Ux i j
lemma part {Y:Finset A}(h:G.good X)(p:Y⊆ X):G.good Y:=fun t=> by obtain ⟨i,z⟩:=h t; exact ⟨i,fun j a=> z _ (p a)⟩
section
variable (h:X.Nonempty)
def win(c:I): A:= Classical.choose (Finset.exists_min_image X (Ux c) h)
lemma enter (c:I): win G h c ∈ X:= (Classical.choose_spec (Finset.exists_min_image X (Ux c) h)).1
lemma floor (x:A)(p:x∈X)(c:I):Ux c (G.win h c)≤ Ux c x:= (Classical.choose_spec (Finset.exists_min_image X (Ux c) h)).2 x p
lemma peak (c:I)(x:A)(p:x∈X)(w:∀ y∈X,Ux c x≤ Ux c y): win G h c=x:= G.inj c (le_antisymm (G.floor h x p c) (w _ (G.enter h c)))
local notation "fo"=> win G h
lemma roof(hX:G.good X):Finset.univ.image fo=X:=Subset.antisymm (by intro y p; obtain ⟨i,-,rfl⟩:=mem_image.mp p; exact G.enter h i) fun x p=>by
 obtain ⟨i,g⟩:= hX x; exact mem_image.mpr ⟨i,mem_univ _,G.peak h i x p g⟩
abbrev posse(c:I): Finset A:=Finset.univ.filter fun x:A=>∀ i:I,i≠c→Ux i (fo i)<Ux i x
variable {c h G}
lemma poss(i:I):G.win h i∈X:=G.enter ..
-- Extender for leading repeat vertex in face S. existence iff posse
lemma tune {x:A} (hv:G.good X)(t:x∈G.posse h c)(i:I)(u:c≠i)(v: fo c=fo i):x∉X ∧ Ux c x < Ux c (fo c):=by
 have hp:= G.roof h hv; have h':= (mem_filter.mp t).2; have yn: x∉ X:=fun hx=>by
    rw [←hp] at hx; obtain ⟨j,l,g⟩:=mem_image.mp hx; by_cases r:j=c
    · exact lt_irrefl _ ((show _<_ from h' i u.symm) |>.trans_eq (by rw [←g,r,v]))
    exact lt_irrefl _ ((h' j r).trans_eq (by rw [←g]))
 refine ⟨yn,?_⟩; obtain ⟨j,p⟩:= hv x; by_cases r:j=c
 · subst j; exact lt_of_le_of_ne (p _ (G.enter h c)) (fun vK=>yn ((G.inj c vK).symm ▸ G.enter h c))
 exact False.elim (not_le.mpr (h' j r) (p _ (G.enter h j)))
lemma regal(Y:Finset A)(e:Y.card=N)(t:Y.Nonempty)(v:G.good Y): Function.Injective (G.win t):=by
 have hp:=Finset.card_image_iff.mp (show (Finset.univ.image (G.win t)).card= (Finset.univ:Finset I).card from by rw [roof _ _ v,e,card_univ]); exact fun i j h=>hp (mem_univ _) (mem_univ _) h
lemma link {x:A}(p:x∉X)(e:G.good (insert x X))(hx:X.card+1=N): ∃ c i:I,c≠i∧ fo c=fo i∧ x∈G.posse h c ∧∀ y∈G.posse h c,Ux c y ≤ Ux c x:=by
 let hy: (insert x X).Nonempty:=insert_nonempty ..; have he:=roof G hy e; have hv:=G.regal _ (by rw [card_insert_of_notMem p,hx]) hy e
 obtain ⟨c,-,g⟩:=Finset.mem_image.mp (show x∈ Finset.univ.image (G.win hy) from by rw [he]; exact mem_insert_self ..); have ht(i:I)(q:i≠c):Ux i (fo i)<Ux i x ∧ G.win hy i= fo i:=by
    have hs:G.win hy i ≠x:=fun b=> q (hv (b.trans g.symm))
    have hl:= (mem_insert.mp (G.enter hy i)).resolve_left hs
    have hz: fo i=G.win hy i:= G.peak h i _ hl (fun y p=> G.floor _ y (mem_insert_of_mem p) i)
    exact ⟨hz.symm ▸ lt_of_le_of_ne (G.floor _ x (mem_insert_self ..) i) (fun u=>hs (G.inj i u)),hz.symm⟩
 obtain ⟨i,-,k⟩:=mem_image.mp (he.symm ▸ mem_insert_of_mem (G.enter h c))
 have hq:i≠c:=fun m=>p (by rw [←g]; rw [m] at k; rw [k]; exact G.enter h c)
 refine ⟨c,i,hq.symm,k.symm.trans (ht _ hq).2, mem_filter.mpr ⟨mem_univ _,fun i v=>(ht _ v).1⟩,?_⟩
 intro y t; obtain ⟨j,w⟩:= e y; by_cases r:j=c; · exact r ▸ w x (mem_insert_self ..)
 exact False.elim (not_le.mpr ((mem_filter.mp t).2 _ r) (w _ (mem_insert_of_mem (G.enter h _))))
lemma ink_f {x:A} (b:x∈G.posse h c)(g:∀ y∈G.posse h c,Ux c y ≤ Ux c x)(v:G.good X)(he:∃ i,c ≠ i∧fo c=fo i): G.good (insert x X) :=by
 obtain ⟨i,u,hv⟩:=he; obtain ⟨s,lu⟩:=G.tune v b i u hv
 intro t; by_cases w:t∈ G.posse h c
 · refine ⟨c,fun j y=>?_⟩; rcases mem_insert.mp y with y |y; exact y.symm ▸ g t w; exact (g t w).trans (lu.le.trans (G.floor _ j y c))
 have p: ¬ ∀ i:I,i≠c→Ux i (fo i)<Ux i t:= fun z=>w (mem_filter.mpr ⟨mem_univ _,z⟩); push_neg at p; obtain ⟨j,p,q⟩:=p; refine ⟨j,fun y t=>?_⟩
 rcases mem_insert.mp t with a|a; exact a.symm ▸ q.trans ((mem_filter.mp b).2 _ p).le; exact q.trans (G.floor _ _ a _)
end
end Gift
end YM.CF.Moen

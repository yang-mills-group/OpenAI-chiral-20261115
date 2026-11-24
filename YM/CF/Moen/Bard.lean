import YM.CF.Moen.Tees
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Moen.Gift
open Function Filter Topology Finset
open scoped Classical BigOperators
variable {I A R: Type*}[Fintype I][DecidableEq I][Fintype A][DecidableEq A][LinearOrder R]
variable (G:Gift I A R)(c:I){X Y:Finset A}
local notation "N"=> Fintype.card I
local notation "Ux"=> G.score
local notation "J"=> G.corner
abbrev faceZ(c:I):Finset A:=(univ.erase c).map J
abbrev banks(G:Gift I A R): Finset (Finset A):=univ.filter fun X=> G.good X∧X.card=N
abbrev pub (X:Finset A):Finset (Finset A):= G.banks.filter fun Y=> X⊆Y
lemma pub_f {X Y:Finset A}:Y∈G.pub X↔G.good Y∧ Y.card=N∧X⊆ Y:=by simp [pub,banks,and_assoc]
lemma facet(c:I)(u:2 ≤ N): (G.faceZ c).card+1=N ∧ G.good (G.faceZ c):=by
 let S:=faceZ G c; constructor
 · simp [S,faceZ]; omega
 intro p; by_cases w:p∈ Set.range J
 · obtain ⟨i,rfl⟩:=w; by_cases v:i=c; · refine ⟨i,fun j t=>le_of_not_gt fun z=>?_⟩; by_cases a:j=J i; rw [a] at z; exact lt_irrefl _ z; exact not_lt.mpr (G.low _ _ a).le z
   refine ⟨i,fun j h=>?_⟩; by_cases ht:j=J i; exact ht.symm ▸ le_rfl; exact (G.low _ _ ht).le
 refine ⟨c,fun j h=>?_⟩; obtain ⟨i,p,rfl⟩:= mem_map.mp h; exact (G.high c i (mem_erase.mp p).1.symm _ w).le
variable {G c}
lemma facetW {X:Finset A}(h:X.Nonempty)(e:∃ i∈X,i∉Set.range J)(c i:I)(w:c≠i)(u:G.win h c=G.win h i): (G.posse h c).Nonempty:=by
 obtain ⟨j,a,b⟩:=e; exact ⟨J c,mem_filter.mpr ⟨mem_univ _,fun k q=>lt_of_le_of_lt (G.floor h j a k) (G.high k c q j b)⟩⟩ -- unused w u yes
lemma trust {c:I}{X:Finset A}(h:X.Nonempty)(w:G.good X)(g:X.card+1=N)(i:I)(p:c≠i)(u:G.win h c=G.win h i)(t:(G.posse h c).Nonempty): ∃ x:A, x∉X∧ x∈ G.posse h c ∧ (insert x X)∈G.pub X∧∀ y∈G.posse h c,Ux c y≤ Ux c x:=by
 obtain ⟨x,a,s⟩:=exists_max_image _ (Ux c) t; have hv:= (G.tune w a i p u).1; exact ⟨x,hv,a,(G.pub_f).mpr ⟨G.ink_f a s w ⟨i,p,u⟩,by rw [card_insert_of_notMem hv,g],subset_insert ..⟩,s⟩
lemma first {X:Finset A}(h:X.Nonempty)(w:G.good X)(g:X.card+1=N)(e:∃ i∈ X,i∉Set.range J): (G.pub X).card=2:=by
 have he:= G.roof h w; have hx: (univ:Finset I).card=X.card+1:= (card_univ).trans g.symm; obtain ⟨i,a,j,b,p,u,s,t⟩:= Moen.bear he hx
 obtain ⟨x,hp,v,hX,tX⟩:=G.trust h w g j p u (G.facetW h e _ _ p u); obtain ⟨y,hq,z,hY,tY⟩:=G.trust h w g i p.symm u.symm (G.facetW h e _ _ p.symm u.symm)
 have hv: insert x X≠ insert y X:=fun q=> by
    have hl:= mem_insert.mp (q ▸ mem_insert_self x X); have hy: x=y:=hl.resolve_right hp; rw [←hy] at z; exact not_le.mpr ((mem_filter.mp z).2 _ p) (G.tune w v j p u).2.le
 have hk:G.pub X={insert x X,insert y X}:=Subset.antisymm (fun u' m=>by
    obtain ⟨s',a',d⟩:= (G.pub_f).mp m; obtain ⟨f,n,rfl⟩:=exists_eq_insert_iff.mpr ⟨d,g.trans a'.symm⟩; obtain ⟨c,r,vr,cr,sc,L⟩:=G.link (h:=h) n s' g
    rcases Moen.bear_w he hx a b p u s t c r (mem_univ _) (mem_univ _) vr cr with ⟨rfl,_⟩|⟨rfl,_⟩
    · rw [G.inj c (le_antisymm (tX _ sc) (L _ v))]; exact mem_insert_self ..
    rw [G.inj c (le_antisymm (tY _ sc) (L _ z))]; simp) (by simp [insert_subset_iff,hX,hY])
 rw [hk, card_pair hv]
variable (G c)
lemma fee (h: 2 ≤ N): (G.pub (G.faceZ c)).card=1:=by
 let X:= G.faceZ c; obtain ⟨hp,hv⟩:=G.facet c h; have hx: X.Nonempty:=card_pos.mp (by change 0 < (G.faceZ c).card; omega)
 have ht(i:I)(p:i≠c): G.win hx i=J i:=by
    exact G.peak _ _ _ (mem_map_of_mem J (mem_erase.mpr ⟨p,mem_univ _⟩)) fun y h=> by by_cases h:y=J i; exact h.symm ▸ le_rfl; exact (G.low _ _ h).le
 obtain ⟨i,w,t⟩:=mem_map.mp (G.enter hx c); have he:= (mem_erase.mp w).1
 have hf: (G.posse hx c).Nonempty:=⟨J c,mem_filter.mpr ⟨mem_univ _,fun j p=>by rw [ht _ p]; exact G.low _ _ (G.corner.injective.ne p.symm)⟩⟩; obtain ⟨x,p,q,u,b⟩:=G.trust hx hv hp i he.symm (by rw [ht i he,t]) hf
 have lu:G.pub X={insert x X}:=Subset.antisymm (fun Y f=>by
    obtain ⟨m,k,g⟩:=G.pub_f.mp f; obtain ⟨a,v,rfl⟩:= exists_eq_insert_iff.mpr ⟨g,hp.trans k.symm⟩; obtain ⟨s,i,w,p',t',hu⟩:= G.link (h:=hx) v m hp; by_cases l:s=c
    · subst s
      rw [G.inj c (le_antisymm (b _ t') (hu _ q))]; exact mem_singleton_self _
    have hl:=(G.tune hv t' i w p').2; rw [ht s l] at hl; by_cases l:a=J s; rw [l] at hl; exact False.elim (lt_irrefl _ hl); exact False.elim (not_le.mpr (G.low _ _ l) hl.le)) (singleton_subset_iff.mpr u)
 rw [show G.faceZ c=X from rfl, lu,card_singleton]
variable (F:A→I)(hp:∀ c:I,F (G.corner c)=c)
abbrev cap (G:Gift I A R)(F:A→I)(c:I):Finset (Finset A):=univ.filter (fun X=>G.good X∧ X.card+1=N∧ X.image F=univ.erase c)
lemma lar {Y:Finset A}(h:G.good Y)(v:Y.card=N)(t:Y.image F≠univ):Even (((G.cap F c).filter fun X=> X⊆Y).card):=by
 let T:=(G.cap F c).filter fun X=> X⊆Y; change Even T.card; rcases T.eq_empty_or_nonempty with e|e; rw [e,card_empty]; exact Even.zero
 have q: (Y.image F)=univ.erase c:=by
    obtain ⟨k,w⟩:=e; obtain ⟨l,t'⟩:=mem_filter.mp w; have ht: univ.erase c⊆ Y.image F:=by rw [← (mem_filter.mp l).2.2.2]; exact image_subset_image t'
    refine Eq.symm (eq_of_subset_of_card_le ht ?_); simp only [card_erase_of_mem (mem_univ _),card_univ]; have he:=Finset.card_lt_card (show Y.image F⊂ univ from Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _,t⟩); rw [card_univ] at he; omega
 have hx:0<N:=by haveI: Nonempty I:=⟨c⟩; exact Fintype.card_pos
 obtain ⟨i,a,j,b,p,u,s,w⟩:=Moen.bear q (show _=_ from by simp only [card_erase_of_mem (mem_univ _),card_univ,v]; omega)
 have he(x:A)(r:x∈Y)(p':Set.InjOn F (Y.erase x)):Y.erase x∈T:=by
    have hp: (Y.erase x).card+1=N:=by rw [card_erase_of_mem r,v]; omega
    have hu: (Y.erase x).image F=univ.erase c:=eq_of_subset_of_card_le (q ▸ image_subset_image (erase_subset ..)) (by rw [card_image_iff.mpr p',card_erase_of_mem (mem_univ _),card_univ]; omega)
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, G.part h (erase_subset ..),hp,hu⟩,erase_subset ..⟩
 have hl:T={Y.erase i,Y.erase j}:=Subset.antisymm (fun X r=>by
    obtain ⟨f,e'⟩:=mem_filter.mp r; obtain ⟨k,l,d⟩:= (mem_filter.mp f).2; have hb:Set.InjOn F X:=card_image_iff.mp (by rw [d,card_erase_of_mem (mem_univ _),card_univ]; omega)
    obtain ⟨x,y,hx'⟩:= exists_eq_insert_iff.mpr ⟨e',l.trans v.symm⟩; by_cases q:x=i; rw [←hx',q] -- check dependency Y card? only goal
    · simp [q ▸ y]
    by_cases q':x=j; · rw [←hx',q',erase_insert (q' ▸ y)]; simp
    have ht:= hb ((mem_insert.mp (hx'.symm ▸ a)).resolve_left (Ne.symm q)) ((mem_insert.mp (hx'.symm ▸ b)).resolve_left (Ne.symm q')) u; exact False.elim (p ht)) (by simp [insert_subset_iff, he i a s, he j b w]) -- hx' replacement.Lean rcases
 rw [hl,card_pair (fun q=> by have hv:i∈ Y.erase i:= q.symm ▸ mem_erase.mpr ⟨p,a⟩; exact notMem_erase _ _ hv)]; decide
include hp c
lemma sand (h: 2 ≤ N):∃ X:Finset A,G.good X∧ X.card=N ∧ X.image F=univ:=by
 let W:=G.cap F c; let T:=G.banks; have hx:(∑ i∈T,(W.filter (fun x=> x⊆i)).card)=∑ i∈W,(G.pub i).card:=by simp_rw [pub,card_filter]; rw [sum_comm] -- matching inst
 obtain ⟨p,v⟩:=G.facet c h; let Z:=G.faceZ c; have hv: Z∈ W:=by
    refine mem_filter.mpr ⟨mem_univ _,v,p,?_⟩; ext j; constructor; · intro u; obtain ⟨x,w,rfl⟩:=mem_image.mp u; obtain ⟨i,r,rfl⟩:=mem_map.mp w; rw [hp]; exact r
    intro t; exact mem_image.mpr ⟨J j,mem_map_of_mem _ t,hp _⟩
 rw [←add_sum_erase W _ hv, G.fee c h] at hx
 have hm: Even (∑ i∈ W.erase Z,(G.pub i).card):=even_sum (s:=W.erase Z) _ (fun x u=> by
    obtain ⟨b,d⟩:= mem_erase.mp u; obtain ⟨v',p',e⟩:= (mem_filter.mp d).2; have he: ∃ i∈ x,i ∉ Set.range J:=by
       by_contra m; push_neg at m; apply b; refine eq_of_subset_of_card_le ?_ (by unfold Z; omega); intro a w; obtain ⟨i,rfl⟩:=m a w; exact mem_map_of_mem _ (show i∈ univ.erase c from by rw [←hp i,←e]; exact mem_image_of_mem _ w)
    rw [G.first (card_pos.mp (by omega)) v' p' he]; decide)
 by_contra m; push_neg at m; have hy: Even (∑ i∈ T,(W.filter fun x=> x ⊆ i).card):=even_sum _ fun i q=>let t:= (mem_filter.mp q).2; G.lar c F t.1 t.2 (m i t.1 t.2)
 obtain ⟨a,u⟩:= hm; obtain ⟨b,v⟩:= hy; change _=1+∑ i∈ W.erase Z,_ at hx; omega
end YM.CF.Moen.Gift

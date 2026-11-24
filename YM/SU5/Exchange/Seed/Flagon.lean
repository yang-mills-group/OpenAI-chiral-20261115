import YM.CF.Vow.Grow
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Rue
namespace TreasuryFog
private def mendV (D:Support (More n))(i:Palot.hook (Site (More n))): Finset (Finset (Force n)):=univ.filter fun (x:Finset (Force n))=> Set.InjOn lordD (x:Set (Force n))∧(x.image lordD=i)∧∀ y∈x, ripeD D y
variable(X:Aura n)(D:Support (More n))(i:Palot.hook (Site (More n)))(F: Force n→ Cipher n)
private lemma bottom_m : mendV D ∅={∅}:=by
 ext j; unfold mendV; constructor; · intro p; exact mem_singleton.mpr (image_eq_empty.mp (mem_filter.mp p).2.2.1)
 intro y; rw [mem_singleton.mp y]; exact mem_filter.mpr ⟨mem_univ _, (by rw [coe_empty]; exact Set.injOn_empty _), image_empty _,fun _ p => False.elim (notMem_empty _ p)⟩
private lemma chartL (X:Aura n)(Y:Support (More n))(x:Force n)(u:x∈motV X (Y ∩ X.val)):lordD x=X ∧ ripeD Y x:= by obtain ⟨p,v⟩:=(mem_filter.mp u).2; exact ⟨p,by unfold ripeD; rw [p]; exact v ⟩ -- cast
private lemma chartW (X:Aura n)(Y:Support (More n))(x:Force n)(u:lordD x=X)(p:ripeD Y x) : x∈motV X (Y∩X.val) := mem_filter.mpr ⟨mem_univ _,u,u ▸ p⟩
private lemma flightT (i: Palot.hook (Site (More n))) : (∏ j∈i,∑ x∈motV j (D∩j.val),F x) = ∑ s∈mendV D i, ∏ j∈s,F j:=by
 induction i using Finset.induction_on with
 | empty=> rw [prod_empty,bottom_m,sum_singleton,prod_empty]
 | @insert a i u ih=>
   let X:=motV a (D∩a.val); let Y:=mendV D i; rw [prod_insert u,ih,sum_mul_sum,←sum_product'];
   have he(x:Force n)(y: Finset (Force n))(v:x∈X)(p:y∈Y):x∉ y:=fun t=> let g:= ((mem_filter.mp p).2.2.1.symm ▸ u); g ((chartL a D x v).1 ▸ mem_image_of_mem lordD t)
   have hh(s:Finset (Force n))(v:Set.InjOn lordD s)(x y:Force n)(u:x∈s)(p:y∈s)(l:lordD x=a)(w:lordD y=a):x=y:= v u p (l.trans w.symm)
   refine sum_bij (fun l _=> insert l.1 l.2) ?_ ?_ ?_ ?_
   · rintro ⟨x,y⟩ v; obtain ⟨l,t⟩:=mem_product.mp v; obtain ⟨k,p,g⟩:= (mem_filter.mp t).2; obtain ⟨hx,hq⟩:=chartL a D x l
     refine mem_filter.mpr ⟨mem_univ _,?_,by rw [image_insert,hx,p],fun z v=> (mem_insert.mp v).elim (fun p=>p ▸ hq) (fun p=>g _ p)⟩
     intro i v j t e; rcases mem_insert.mp v with rfl|v<;> rcases mem_insert.mp t with rfl|t; rfl; exact False.elim (u (p ▸ (hx ▸ (e.symm ▸ (mem_image_of_mem lordD t))))); exact False.elim (u (p ▸ (hx ▸ (e ▸ (mem_image_of_mem lordD v))))); exact k v t e -- tunes
   · rintro ⟨x,y⟩ v ⟨z,w⟩ p t; obtain ⟨l,q⟩:=mem_product.mp v; obtain ⟨u₁,u₂⟩:= mem_product.mp p; have hs:insert x y=insert z w:=t
     have hz:x=z:=by
        obtain rfl|h:=mem_insert.mp (show x∈ insert z w from hs ▸ mem_insert_self x y); rfl; exact False.elim (he _ _ l u₂ h)
     subst z; rw [Prod.mk.injEq]; refine ⟨rfl,?_⟩; simpa only [erase_insert (he _ _ l q),erase_insert (he _ _ u₁ u₂)] using congrArg (fun i:Finset _=> i.erase x) hs -- tune beta simp
   · intro s p; obtain ⟨x,k,z⟩:= (mem_filter.mp p).2; obtain ⟨y,h,f⟩:= mem_image.mp (k.symm ▸ mem_insert_self ..); have hu:y∈X:=chartW a D y f (z y h)
     refine ⟨(y,s.erase y),mem_product.mpr ⟨hu, mem_filter.mpr ⟨mem_univ _, fun _ p _ t v=>x (erase_subset _ _ p) (erase_subset _ _ t) v,?_, fun _ p=>z _ (erase_subset _ _ p)⟩⟩,insert_erase h⟩
     ext b; constructor
     · intro v; obtain ⟨l,p,rfl⟩:= mem_image.mp v; obtain ⟨e,t⟩:= mem_erase.mp p; exact (mem_insert.mp (k ▸ mem_image_of_mem lordD t)).resolve_left fun w=> e (x t h (w.trans f.symm))
     intro p; obtain ⟨l,v,w⟩:=mem_image.mp (k.symm ▸ mem_insert_of_mem p); exact mem_image.mpr ⟨_,mem_erase.mpr ⟨fun g=> u ((w.symm.trans ((congrArg _ g).trans f)) ▸ p),v⟩,w⟩ -- tune g subst
   rintro ⟨x,y⟩ p; exact (prod_insert (he _ _ (mem_product.mp p).1 (mem_product.mp p).2)).symm
variable(V:Orbit n)(K:Cusp n)
local notation "Ω"=> flags P.threshold V.1
-- variant proof of Vow.themeK: don't assume the particular budget distribution
-- on a support. use to preserve EXACT zero-pin Force addresses and values
-- (otherwise replacing them all by budgetR could pick up the same
-- energy but not be eligible to ask on that very pin).
abbrev settleK (X:ForceBudget n)(i:Aura n)(D:Support (More n)):Copy n:=∑ s∈motV i D, X s
lemma settleMask (h : FleetS P.threshold V.1)(A:ForceBudget n)(s:∀ (y:Aura n),fuelH (flags P.threshold V.1) y→ settleK A y (Ω∩y.val) V= K y (Ω∩y.val) V) : beamP P K V=fueled P A V:=by
 let F(i):= clamp P i (A i) V; have ht(y:Aura n)(u:fuelH Ω y): hailV Ω K V y= ∑ i∈ motV y (Ω∩y.val),F i:=by
    let S:=Ω∩y.val; let t:= bassH y; let G:= hailV Ω K V y; have hp(i:Force n)(p:i∈motV y S): boundF i P V.1:=by
       apply (shoreK _ _ h _).mp; obtain ⟨l,v⟩:= (mem_filter.mp p).2; change Disjoint ((lordD i).val\extraD i) Ω; rw [l,v]; exact Finset.disjoint_left.mpr fun {x} g p=> (mem_sdiff.mp g).2 (mem_inter.mpr ⟨p,(mem_sdiff.mp g).1⟩)
    rw [hailV,←s y u,settleK,Finset.sum_apply]; exact Finset.sum_congr rfl (fun i h=>(show F i=A i V from if_pos (hp i h)).symm)
 let Q:= fun s: Finset (Force n)=> coverF P s V.1 ∧ Set.PairwiseDisjoint (s:Set (Force n)) (fun x=> x.val.1.val.2); let W:=univ.filter Q
 have he{p: Palot.hook (Site (More n))}(z:p∈highV Ω)(s:Finset (Force n)): s∈ W∧s.image lordD=p ↔ s∈mendV Ω p:=by
    obtain ⟨r,t,v⟩:= (mem_filter.mp z).2; rw [show (s∈W)↔ Q s from mem_filter.trans (and_iff_right (mem_univ _)), mendV,mem_filter,and_iff_right (mem_univ _)]
    constructor
    · rintro ⟨⟨l,h⟩,k⟩; refine ⟨fun i y m p t=>?_ ,k,fun i g=>?_⟩
      · by_contra t'; refine Finset.not_disjoint_iff_nonempty_inter.mpr ?_ (h y p t'); change ((lordD i).val∩(lordD m).val).Nonempty; rw [t,inter_self]; exact (lordD m).property
      apply Finset.Subset.antisymm; exact fun x v=>mem_inter.mpr ⟨l ▸ mem_biUnion.mpr ⟨i,g,v⟩,i.property.2 v⟩
      intro x y; obtain ⟨y,u⟩:= mem_inter.mp y; obtain ⟨j,v,w⟩:= mem_biUnion.mp (l.symm ▸ y); by_cases q:j=i; exact q ▸ w; exact False.elim (Finset.disjoint_left.mp (h v g q) (j.property.2 w) u)
    rintro ⟨u,o,H⟩; refine ⟨⟨?_ ,fun i a j b p=> r _ (o ▸ mem_image_of_mem lordD a) _ (o ▸ mem_image_of_mem lordD b) (fun l=>p (u a b l))⟩,o⟩
    unfold coverF; ext i; constructor
    · intro w; obtain ⟨b,g,h⟩:= mem_biUnion.mp w; exact (mem_inter.mp (show i∈ Ω ∩ _ from (H b g) ▸ (show i∈extraD b from h))).1
    intro y; obtain ⟨l,hZ,w⟩:= mem_biUnion.mp (t y); obtain ⟨x,g,f⟩:= mem_image.mp (o.symm ▸ hZ); rw [←f] at w; refine mem_biUnion.mpr ⟨x,g,?_⟩; change i∈ extraD x; rw [show extraD x= _ from H x g]; exact mem_inter.mpr ⟨y,w⟩
 unfold beamP Palot.Hac fueled; rw [←sum_filter, ←sum_fiberwise_of_maps_to (t:=highV Ω) (g:=fun s:Finset (Force n)=> s.image lordD) (s:=W) ?_]; swap
 · intro i p; obtain ⟨l,v⟩:= (mem_filter.mp p).2; refine mem_filter.mpr ⟨mem_univ _,fun j x k h t=>?_ ,fun k u=>?_ ,fun j b y=>?_⟩
   · obtain ⟨i,u,rfl⟩:= mem_image.mp x; obtain ⟨q,p,rfl⟩:= mem_image.mp h; exact v u p (fun g=>t (congrArg _ g))
   · obtain ⟨i,b,w⟩:= mem_biUnion.mp (l.symm ▸ u); exact mem_biUnion.mpr ⟨_,mem_image_of_mem lordD b,i.property.2 w⟩
   obtain ⟨i,tX,rfl⟩:=mem_image.mp b; obtain ⟨j,w⟩:=i.property.1; exact Finset.disjoint_left.mp y (i.property.2 w) (l ▸ mem_biUnion.mpr ⟨i,tX,w⟩)
 apply sum_congr rfl; intro i p; rw [prod_congr rfl (fun j u=>ht j ((mem_filter.mp p).2.2.2 _ u)),flightT]; exact sum_congr (Finset.ext fun j=> (mem_filter.trans (he p j)).symm) (fun _ _=>rfl)
lemma eachFace (X:Aura n)(e:D.Nonempty)(u:D⊆X.val):settleK (budgetR K) X D= K X D:=by
 let H(i):=budgetR K i; let S:=motV X D
 have hp(i)(v:i∈S): H i=bassH X • K X D:=by obtain ⟨k,l⟩:=(mem_filter.mp v).2; unfold H budgetR; rw [k,l]
 have hx:D∈ fullD X:=mem_filter.mpr ⟨mem_univ _,e,u⟩; change ∑ i∈S,H i= _; rw [sum_congr rfl hp, sum_const, countV X hx, ←Nat.cast_smul_eq_nsmul ℝ]; exact smul_inv_smul₀ (show (X.val.card:ℝ)≠0 from by exact_mod_cast (card_pos.mpr X.property).ne') _
lemma settle0 (X:ForceBudget n)(i:Aura n) : settleK X i ∅=0:=sum_eq_zero fun j (y:j∈motV i ∅)=> by have ht:= (mem_filter.mp y).2.2; exact False.elim (j.property.1.ne_empty ht)
lemma settle_add (X:Aura n)(D:Support (More n))(A B':ForceBudget n): settleK (A+B') X D= settleK A X D+settleK B' X D:=by simp [settleK,sum_add_distrib]
lemma settle_sub (X:Aura n)(D: Support (More n))(A B': ForceBudget n): settleK (A-B') X D=settleK A X D-settleK B' X D:=by simp [settleK,sum_sub_distrib]
lemma settleSelf (h:FleetS P.threshold V.1)(A:ForceBudget n) : beamP P (settleK A) V= fueled P A V:=settleMask V _ h A fun _ _=>rfl
-- same with additive displacement at each support
lemma budgetDisplace (h:FleetS P.threshold V.1)(A F₀:ForceBudget n) (p:∀ i:Aura n,fuelH Ω i→ settleK F₀ i (Ω∩i.val) V= settleK A i (Ω∩i.val) V):beamP P K V=fueled P (A+(budgetR K-F₀)) V:=by
 apply settleMask; exact h; intro y v; have e:(Ω∩y.val).Nonempty:= Finset.not_disjoint_iff_nonempty_inter.mp (fun D=> v D.symm)
 rw [settle_add,settle_sub,eachFace _ _ y e inter_subset_right,Pi.add_apply,Pi.sub_apply,p _ v]; abel
end TreasuryFog
end YM.CF.Vow

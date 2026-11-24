import YM.CF.Eire.Pace
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Eire
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
variable {N P B:Side}(S:StepData (Domain N B) (Domain P B)){r D:ℕ}
variable (L L':Ride S)
local notation "bay"=> Stilo.bay
open Rush Scroll Paige Vault Phase Acorn Spire
variable {A:Side}{j k:ℕ}{o:Odd A.val}{Y:Pricing j A o (Thread j)}{e:ℝ}{q:Grasp Y B e}{I:Aim (mid P B)}{M:Male}{α K K' t a d C H:ℝ}
variable (V: ∀ A:Support (Domain P B),Lend P B e A)(X:Tints P B e)
variable(T T' U U':Pane (mid P B))(G:Ids (mid P B))(D)
-- finite exact allocation
open scoped Classical
abbrev crewL (F:Finset (Hos S r)):= Finset.univ.filter fun i:Finset (Kite S r)=> pureK S i ∧ liftK S i=F
variable {O:Stores S}(g:Cheer T U O e D r)
set_option maxHeartbeats 800000 in
lemma choose_l (l:List (Hos S r))(u:l.Nodup)(h:l.toFinset ⊆ blip S O r): ∑ i ∈ crewL S l.toFinset, paint S D V X T U G i l= kindle e X V G g l:=by
 induction l with
 | nil=>
    rw [kindle,sum_eq_single ∅]; rfl; intro i h l; obtain ⟨k,hk⟩:=Finset.nonempty_iff_ne_empty.mpr l; have ht: k.1∈ liftK S i:= mem_image_of_mem _ hk; rw [(mem_filter.mp h).2.2] at ht; exact (notMem_empty k.1 ht).elim
    intro p; exact False.elim (p (mem_filter.mpr ⟨mem_univ _,fun i t=>False.elim (notMem_empty i t), by simp [liftK]⟩))
 | cons i l ih=>
    rw [List.toFinset_cons] at h; let E:=Support (Domain P B); let F:= l.toFinset; let Z:=insert i F; let K:=g.shiftK F i h; rw [List.nodup_cons] at u; have hp:i∉ F:=fun v=>u.1 (List.mem_toFinset.mp v); rw [List.toFinset_cons,kindle,dif_pos h,← ih u.2 ((subset_insert ..).trans h),sum_mul_sum, ←sum_product']
    let M:=Finset.univ (α:= Support (Domain P B) × Support (Domain P B)) ×ˢ crewL S F; let f(a:E×E)(X:Finset (Kite S r)):= insert ((i,a):Kite S r) X
    have he(a:E×E)(p:Finset (Kite S r))(x:p∈ crewL S F): i∉liftK S p∧f a p∈crewL S Z∧ legend S (f a p) i={(i,a)}∧(f a p).erase (i,a)=p:=by
       let A:=f a p; obtain ⟨g,k⟩:= (mem_filter.mp x).2; have ho:i∉liftK S p:= by simpa only [k] using hp
       have hu:liftK S A= Z:=by rw [show liftK S A=insert i (liftK S p) from image_insert ..,k]
       have hx:i∈Z:=mem_insert_self ..; have ht:pureK S A:=by
         refine capPure S A ?_ ?_
         · rw [hu]; exact Set.PairwiseDisjoint.subset (stem_d ..) (Finset.coe_subset.mpr h) -- tune order
         intro j t l v H; rcases mem_insert.mp t with p|p <;> rcases mem_insert.mp v with q|q
         · exact p.trans q.symm
         · subst j; exact False.elim (ho ((show i=l.1 from H).symm ▸ mem_image_of_mem Prod.fst q))
         · subst l; exact False.elim (ho ((show j.1=i from H) ▸ mem_image_of_mem Prod.fst p))
         exact proud_p S _ g p q H
       exact ⟨ho,mem_filter.mpr ⟨mem_univ _,ht,hu⟩,solo S A i ht a (mem_insert_self ..),erase_insert (fun g=>ho (mem_image_of_mem Prod.fst g))⟩
    symm; let A(X:E×E×E):=X -- unused
    refine sum_bij (fun a _=>f a.1 a.2) (fun a v=> (he _ _ (mem_product.mp v).2).2.1) ?_ ?_ ?_
    · rintro ⟨a,P⟩ v ⟨b,R⟩ p he'; obtain ⟨u,x,t,k⟩:=he a P (mem_product.mp v).2; obtain ⟨j,g,q,h⟩:= he b R (mem_product.mp p).2; change f a P=f b R at he'; rw [he',q] at t; simp only [singleton_inj, Prod.mk.injEq,true_and] at t; subst b; rw [he',h] at k; rw [k]
    · intro a v; obtain ⟨p,b⟩:= (mem_filter.mp v).2; have ht:i∈liftK S a:= b.symm ▸ mem_insert_self ..; obtain ⟨j,u,z⟩:= mem_image.mp ht; let P:= a.erase j; have hp':f j.2 P=a:=by simp only [f,P,←z]; change insert j _= _; exact insert_erase u
      refine ⟨(j.2,P), mem_product.mpr ⟨mem_univ _,mem_filter.mpr ⟨mem_univ _,p.subset (Finset.coe_subset.mpr (erase_subset ..)),?_⟩⟩,hp'⟩
      ext w; constructor
      · intro q; obtain ⟨k,t,rfl⟩:=mem_image.mp q; obtain ⟨l,u'⟩:=mem_erase.mp t; exact (mem_insert.mp (b ▸ mem_image_of_mem Prod.fst u')).resolve_left (fun y=> l (proud_p S a p u' u (y.trans z.symm))) -- z orientation
      intro t; obtain ⟨x,k,rfl⟩:= mem_image.mp (show w∈ liftK S a from b.symm ▸ mem_insert_of_mem t); exact mem_image_of_mem _ (show x∈P from mem_erase.mpr ⟨fun h=> hp ((congrArg Prod.fst h).trans z ▸ t),k⟩) -- parentheses
    rintro ⟨a,k⟩ g'; let L:= f a k; have hk : k∈ crewL S F:=(mem_product.mp (show (a,k)∈ M from g')).2; have v:L∈crewL S Z:=(he a k hk).2.1; have hv:= (mem_filter.mp v).2.2; have hq: legend S L i={(i,a)}:= (he a k hk).2.2.1; change (Scion.stock e (danceL S i.val r) X V K G a*paint S D V X T U G k l)= paint S D V X T U G L (i::l); rw [paint,rankG,if_pos (hv.symm ▸ mem_insert_self ..), hq,sum_singleton,show clipM S L l=F from ?_, show paint S D V X T U G L l=paint S D V X T U G k l from pray S D V X T U G (i,a) k l u.1]; swap
    · unfold clipM; rw [(mem_filter.mp v).2.2]; exact inter_eq_right.mpr (subset_insert ..)
    congr 1; unfold postM; rw [dif_pos (show printG S D T U F i∈ MonoX P B e (danceL S i.val r) from (g.shiftK F i h).property)]; try rfl
-- relation between filters once
lemma lightP (g:Stores S)(i: Finset (Kite S r)): i∈ crewL S (blip S g r) ↔ pureK S i∧ cook S i=g:=by
 rw [crewL,mem_filter,and_iff_right (mem_univ _)]; constructor; rintro ⟨u,v⟩; exact ⟨u,(show cook S i=g by rw [cook,v,stem_t])⟩; rintro ⟨p,rfl⟩; exact ⟨p,(cooked S i p).symm⟩
lemma group_pres (L:List (Hos S r))(p:L.Nodup)(u:∀ i∈blip S O r,i∈L): ∑ i∈ crewL S (blip S O r), paint S D V X T U G i L=kindle e X V G g (L.filter fun i=> i∈ blip S O r):=by
 let Q:= L.filter fun i=> i∈ blip S O r; have he:Q.toFinset=blip S O r:= by ext; simp only [Q,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]; exact ⟨And.right,fun v=>⟨u _ v,v⟩⟩
 change _=kindle _ _ _ _ _ Q; rw [← choose_l _ _ _ _ _ _ _ g Q (List.Nodup.filter _ p) he.le,he]; apply sum_congr rfl; intro i v; let P:=(mem_filter.mp v).2.2; apply Eq.symm; unfold Q; simp_rw [← P,jug]
end YM.CF.Eire

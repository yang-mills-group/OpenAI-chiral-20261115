import YM.CF.Palot.Pal
import YM.Push.ABSOLUTE_SUMS.Distinct
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Palot
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo
open scoped Classical
variable {A I E:Type*}[Fintype A][DecidableEq A][Fintype I][DecidableEq I][CommSemiring E]
variable {n:Side}
open RG Push Push.AbsoluteSums Push.AbsoluteSums.Trees
local notation "bay"=>Stilo.bay
lemma joinsB (H R:Crowd A) : bay (H⊔R)=bay H∪bay R:=by
 ext i; rw [mem_union]; constructor; swap; · intro h; exact h.elim (fun g=>bay_m le_sup_left g) (fun g=>bay_m le_sup_right g)
 intro h; have hp:TransGen (fun a b=>rail H a b∨rail R a b) i i:= (mem_filter.mp (bayH.mp h)).2
 suffices g:∀ x y, TransGen (fun a b=>rail H a b∨rail R a b) x y→x∈bay H ∨ x∈bay R from g _ _ hp
 intro x y v; induction v with|single a=> exact a.elim (fun p=> Or.inl (tract x _ p).1) (fun p=>Or.inr (tract x _ p).1)| tail _ _ ih=> exact ih
def rhythm (X:I→Finset A)(P:Finset I):Crowd A:= P.sup (fun i=> beamH (X i))
lemma beats (X:I→Finset A)(P:Finset I) : bay (rhythm X P)=P.biUnion X:=by induction P using Finset.induction_on with | empty=> rw [rhythm,sup_empty,bayB]; simp | insert i P l ih=> rw [show rhythm _ _=beamH (X i)⊔rhythm X P from (by simp [rhythm]),joinsB,bay_beam,ih,biUnion_insert]
lemma break_h (X:I→ Support n)(v:∀ i,(X i).Nonempty)(S:leaf (Site n))(P: Finset I)(h:rhythm X P=beamH S.val): Ac.Spark X P∧ P.biUnion X=S.val:=by
 have hU : P.biUnion X=S.val:= (beats X P).symm.trans ((congrArg Stilo.bay h).trans (bay_beam _))
 refine ⟨⟨?_,?_⟩,hU⟩
 · contrapose! hU; rw [hU]; simpa using (nonempty_iff_ne_empty.mp S.property).symm
 intro i t j u; by_contra f; let L:= Ac.burst X P i; let R:= P \ L; have hL:L⊆P:=filter_subset ..
 have hi:i∈ L:= (Ac.bright X ..).mpr ⟨t,.refl⟩; have hj:j∈R:=mem_sdiff.mpr ⟨u,fun w=>f ((Ac.bright X ..).mp w).2⟩
 have hy: rhythm X P= rhythm X L⊔ rhythm X R:=by nth_rw 1 [← Finset.union_sdiff_of_subset hL]; rw [rhythm,sup_union]; rfl
 let C':=rhythm X L; let D:=rhythm X R; have hz:Disjoint (bay C') (bay D):=by
    unfold C' D; rw [beats,beats]; refine Finset.disjoint_left.mpr fun {x} g p=>?_ ; obtain ⟨y,b,V⟩:=mem_biUnion.mp g; obtain ⟨z,k,M⟩:=mem_biUnion.mp p; obtain ⟨l,q⟩:= mem_sdiff.mp k; have hv:=((Ac.bright X i y).mp b).2; exact q ((Ac.bright X i z).mpr ⟨l,Relation.ReflTransGen.tail hv (show Ac.bonds X P y z from ⟨hL b,l,x,V,M⟩)⟩)
 obtain ⟨x,hx⟩:=v i; obtain ⟨z,hz'⟩:=v j; have he:x∈bay C':= (beats X L).symm ▸ mem_biUnion.mpr ⟨i,hi,hx⟩; have hg:z∈bay D:= (beats X R).symm ▸ mem_biUnion.mpr ⟨j,hj,hz'⟩
 have hl : rail (C'⊔D) x z:= by rw [show C'⊔D= beamH S.val from hy.symm.trans h]; exact mem_product.mpr ⟨hU ▸ mem_biUnion.mpr ⟨i,t,hx⟩,hU ▸ mem_biUnion.mpr ⟨j,u,hz'⟩⟩
 exact (hut hz).mp hl|>.elim (fun p=> Finset.disjoint_left.mp hz (tract _ _ p).2 hg) (fun p=>Finset.disjoint_left.mp hz he (tract _ _ p).1)
variable {J:Type*}[Fintype J][DecidableEq J]
def ticketSet (h:J→I)(P:Finset I):Finset (Finset J):= univ.filter fun l=> Set.InjOn h l ∧ l.image h=P
def turnY(h:J→I)(P:Finset I)(X:J→Finset A)(F:J→ℝ):Track (Crowd A) ℝ:= ∑ i ∈ ticketSet h P, Pi.single (rhythm X i) (∏ j∈ i,F j)
lemma turn_card (h:J→I)(P:Finset I)(l:Finset J)(v:l∈ticketSet h P):l.card=P.card:=by obtain ⟨f,g⟩:=(mem_filter.mp v).2; rw [←g,Finset.card_image_of_injOn f]
lemma turn_empty (h:J→I)(X:J→Finset A)(F:J→ℝ): turnY h ∅ X F=ownH ℝ _:=by
 unfold turnY; rw [sum_eq_single ∅]; simp [rhythm,ownH]
 · intro i p g; exact False.elim (g (card_eq_zero.mp (turn_card h ∅ i p)))
 simp [ticketSet]
def tea(h:J→I)(X:J→Finset A)(F:J→ℝ)(i:I):Track (Crowd A) ℝ := ∑ l:J with h l=i, Pi.single (beamH (X l)) (F l)
lemma pav_sum {R:Type*}[AddCommMonoid R](B:Crowd A)(f:I→Track (Crowd A) R)(T:Finset I): view B (∑ i∈T,f i)=∑ i∈T, view B (f i):=map_sum (vAdd B) .. -- tune
lemma turn_next(h:J→I)(H:I)(X:J→Finset A)(F:J→ℝ)(P:Finset I)(p:H∉P):turnY h (insert H P) X F=crank (tea h X F H) (turnY h P X F):=by
 ext i : 1; apply proves; intro K _
 rw [view_crank, tea,turnY,turnY,pav_sum,pav_sum,pav_sum, sum_mul_sum,←sum_product']; symm
 refine Finset.sum_bij (fun q _=>insert q.1 q.2) ?_ ?_ ?_ ?_ -- need use facts repeatedly -- tune
 · rintro ⟨a,b⟩ hx; obtain ⟨l,v⟩:=mem_product.mp hx; obtain ⟨f,g⟩:= (mem_filter.mp v).2; have hu:= (mem_filter.mp l).2; refine mem_filter.mpr ⟨mem_univ _,?_, (by dsimp only; rw [image_insert, hu,g])⟩
   intro i hb j hv e; rcases mem_insert.mp (show i∈ insert a b from hb) with rfl|t<;> rcases mem_insert.mp (show j∈insert _ b from hv) with rfl|w
   · rfl
   · exact False.elim (p ((by rw [←hu,e,←g]; exact mem_image_of_mem _ w : H∈P)))
   · exact False.elim (p ((by rw [←hu,←e,←g]; exact mem_image_of_mem _ t : H∈P)))
   exact f t w e
 · rintro ⟨a,b⟩ q ⟨x,y⟩ v H'; change insert a b=insert x y at H'
   obtain ⟨l,t⟩:=mem_product.mp q; obtain ⟨z,u⟩:=mem_product.mp v; have ht:=(mem_filter.mp t).2.2; have hu:=(mem_filter.mp u).2.2; have hg := (mem_filter.mp l).2; have hh:= (mem_filter.mp z).2
   have hx(i)(s:i∈b): h i ≠ H:=fun v=> p (v ▸ ht ▸ mem_image_of_mem h s) -- tune
   have hf(i)(s:i∈ y): h i ≠ H:=fun v=> p (v ▸ hu ▸ mem_image_of_mem h s)
   have he:x=a:= (mem_insert.mp (H'.symm ▸ mem_insert_self x y)).resolve_right (fun t=> hx x t hh); subst x
   exact Prod.ext rfl (by rw [← Finset.erase_insert (s:=b) (a:=a) (fun s=>hx a s hg),H', Finset.erase_insert (fun s=> hf a s hh)]) -- tune change
 · intro y v; obtain ⟨f,g⟩:=(mem_filter.mp v).2; have he:H∈ y.image h:= g.symm ▸ mem_insert_self ..; obtain ⟨a,t,u⟩:= mem_image.mp he
   have hx:y.erase a∈ticketSet h P:=by
      refine mem_filter.mpr ⟨mem_univ _,Set.InjOn.mono (show ↑(y.erase a) ⊆ (↑y:Set J) from (fun _ z=>mem_of_mem_erase z)) f,?_ ⟩ -- syntax mono
      ext i; rw [mem_image]; constructor
      · rintro ⟨k,hk,rfl⟩; have hp:= mem_of_mem_erase hk; exact (mem_insert.mp (g ▸ mem_image_of_mem h hp)).resolve_left fun e=> (mem_erase.mp hk).1 (f hp t (e.trans u.symm))
      intro w; obtain ⟨z,v,e⟩:=mem_image.mp (g.symm ▸ mem_insert_of_mem w); exact ⟨z,mem_erase.mpr ⟨fun l=> p (by rw [←e,l,u] at w; exact w),v⟩,e⟩
   exact ⟨(a,y.erase a),mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,u⟩,hx⟩,insert_erase t⟩
 rintro ⟨i,Y⟩ q; obtain ⟨l,v⟩:= mem_product.mp q; obtain ⟨-,t⟩:= mem_filter.mp l; obtain ⟨-,hx⟩:= (mem_filter.mp v).2; have he:i∉ Y:= fun u=> p (by rw [←hx,←t]; exact mem_image_of_mem _ u)
 simp_rw [singleV]; simp only [rhythm,sup_insert, prod_insert he,sup_le_iff]
 aesop
end YM.CF.Palot

import YM.CF.BProof.Vogue.Sweep
import YM.CF.BProof.Shade.Stamp
/-! Arithmetic overlap stamp of component families. Instances discrete as chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Vogue
open Function Filter Relation Set MeasureTheory ProbabilityTheory Skye Spire Lattice Wilson Mesh
open scoped Topology BigOperators NNReal ENNReal Classical
variable {I K:Type*}{n:Side}
variable (M:Finset (Seat n))(r k L:ℕ)
def Fleets: Finset (Finset (Seat n)):= (((Finset.univ:Finset (reach n)).image (soup M r)).erase ∅)
def Bubb (i:reach n):= (soup M r i).Nonempty
lemma ft {i:reach n}(p:Bubb M r i): soup M r i∈ Fleets M r:= Finset.mem_erase.mpr ⟨(Finset.nonempty_iff_ne_empty.mp p), Finset.mem_image_of_mem (soup M r) (Finset.mem_univ i)⟩
lemma cashS (x:Fleets M r): x.val.Nonempty:=Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp x.property).1
lemma passes(x:Fleets M r):∃ i: reach n,soup M r i=x.val:=by obtain ⟨i,_,hi⟩:= Finset.mem_image.mp (Finset.mem_erase.mp x.property).2; exact ⟨i,hi⟩
variable {M r k L}
open Finset
lemma bubble_s {r k:ℕ}{x:reach n}(h:k≤r)(p:Bubb M k x): Bubb M r x:= (pieV ..).mpr fun e=> (pieV ..|>.mp p) (e.mono_right (Corona.halo_mono h (Finset.Subset.refl _)))
lemma feeway {i: reach n}{x y:Seat n}(p:x∈ ends i)(q:y∈ ends i): separation x y ≤ 1:=by
 rcases mem_insert.mp p with g|g <;> rcases mem_insert.mp q with h|h
 · simp [g,h]
 · rw [g,mem_singleton.mp h]; exact Nest.nearV _ (posDir i.2)
 · rw [h,mem_singleton.mp g,separation_comm]; exact Nest.nearV _ (posDir i.2)
 simp [mem_singleton.mp g,mem_singleton.mp h]
lemma width {x y:Seat n} (p:legs M r x y): legs M r y x:= ⟨p.2.1,p.1,(separation_comm ..).trans_le p.2.2⟩
private lemma travelp {x y:Seat n}(p:ReflTransGen (legs M r) x y):ReflTransGen (legs M r) y x:=by induction p with|refl=>exact .refl| tail p i ih=>exact .head (width i) ih
lemma soupInc {i:reach n}{x y:Seat n}(h:x∈ Cake M r i)(g:y∈ Cake M r i): ReflTransGen (legs M r) x y:=by
 obtain ⟨x',p,hx⟩:= (mem_filter.mp h).2; obtain ⟨y',q,hy⟩:= (mem_filter.mp g).2; apply ReflTransGen.single; refine ⟨(mem_filter.mp h).1,(mem_filter.mp g).1,?_⟩; apply (separation_triangle x x' y).trans; have ht:= separation_triangle x' y' y; rw [separation_comm x' x] at hx; have hs:=feeway (i:=i) p q; omega
lemma full {i:reach n}{x y:Seat n}(p:x∈soup M r i)(g:ReflTransGen (legs M r) x y): y∈soup M r i:=by induction g with|refl=>exact p|tail h g ih=>obtain ⟨v,k,t⟩:= (mem_filter.mp ih).2; exact mem_filter.mpr ⟨g.2.1,v,k,t.tail g⟩
lemma internal {i:reach n}{x y:Seat n}(p:x∈ soup M r i)(q:y∈ soup M r i): ReflTransGen (legs M r) x y:=by
 obtain ⟨v,p,e⟩:=(mem_filter.mp p).2; obtain ⟨w,q,f⟩:=(mem_filter.mp q).2; exact ((travelp e).trans (soupInc p q)).trans f
lemma only {i j:reach n}(p:¬Disjoint (soup M r i) (soup M r j)): soup M r i = soup M r j:=by
 obtain ⟨x,l,g⟩:=Finset.not_disjoint_iff.mp p; ext w; exact ⟨fun e=> full g (internal l e), fun e=> full l (internal g e)⟩
variable (M r)
lemma separates : Pairwise (fun i j:Fleets M r=>Disjoint i.val j.val):=by
 intro i j p; obtain ⟨x,hx⟩:= passes M r i; obtain ⟨y,hy⟩:=passes M r j; by_contra h; apply p; exact Subtype.ext (hx.symm.trans ((only (by rw [hx,hy]; exact h)).trans hy))
variable {M r}
-- bucket d in active radius only when Spicy Basic at smaller r; not all edges!
lemma lives_space (h:k+1+(k+1)+L≤2*r+20)(v:k≤r)(i j: reach n)(p:soup M r i ≠ soup M r j)(vi:Bubb M k i)(vj:Bubb M k j): L < separation i.1 j.1:=by
 obtain ⟨x,q⟩:=vi; obtain ⟨y,z⟩:=vj; obtain ⟨x,vx,_⟩:=(mem_filter.mp q).2; obtain ⟨y,vy,_⟩:= (mem_filter.mp z).2; have hx:x ∈soup M r i:= soup_p _ _ _ (cake_p _ _ _|>.symm ▸ (by have ht:= Finset.mem_inter.mp ((cake_p M k i) ▸ vx); exact Finset.mem_inter.mpr ⟨ht.1,Corona.halo_mono v (Finset.Subset.refl _) ht.2⟩)); have hy:y∈ soup M r j:=soup_p _ _ _ ((cake_p ..).symm ▸ (by have ht:= Finset.mem_inter.mp ((cake_p ..) ▸ vy); exact Finset.mem_inter.mpr ⟨ht.1,Corona.halo_mono v (Finset.Subset.refl _) ht.2⟩))
 obtain ⟨x',hx',g⟩:= (mem_filter.mp vx).2; obtain ⟨y',hy',g'⟩:=(mem_filter.mp vy).2; by_contra! H
 have hb: legs M r x y:= by refine ⟨(mem_filter.mp vx).1,(mem_filter.mp vy).1,?_⟩; apply (separation_triangle x i.1 y).trans; rw [separation_comm x]; have t0:=separation_triangle i.1 x' x; have t1:=separation_triangle j.1 y' y; have ht:=separation_triangle i.1 j.1 y; have he:=feeway (i:=i) (mem_insert_self ..) hx'; have hf:=feeway (i:=j) (mem_insert_self ..) hy'; omega
 exact p (only (fun k=>Finset.disjoint_left.mp k (full hx (ReflTransGen.single hb)) hy))
end YM.CF.BProof.Vogue

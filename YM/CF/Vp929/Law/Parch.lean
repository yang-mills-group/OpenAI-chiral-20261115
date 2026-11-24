import YM.CF.Vp929.Law.Overlay
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
set_option linter.unusedSectionVars false
namespace YM.CF.VolumeCape
open Lattice Finset Function
open scoped Classical
namespace Rooms
variable {L : Set Rooms} {r:Rooms→ℕ} {x y z w t:Rooms}{B:ℕ}
def Slayer (r:Rooms→ℕ)(s:ℕ):Prop:=∀ x y,x.bounded s → y.bounded s → y.meets x→ r y=r x→ y=x

def batch(r:Rooms→ℕ)(L:Set Rooms):ℕ→Set Rooms
 | 0=> Spread r L
 | j+1=>Spread r {f|∃ y∈batch r L j, f.facet y}
variable (B L r)
structure Canopy : Prop where
 ample :∀ y∈L, bounded y B
 top:∀ y∈ L,y.dim=4
 stand:∀ t,t.Tiny→∃ y∈L,t≤y
 localOrder: Slayer r B
variable {r L B}(h:Canopy L r B)
local notation "B'" j:max=> batch r L j
include h
lemma graft(i:ℕ)(v:x∈ B' (i+1)):∃ y∈B' i, x.boundary y:=by obtain ⟨w,⟨y,e,p⟩,v,t⟩:=v; exact ⟨y,e,boundary_mono (proper p) (diced_le v)⟩
lemma shoulder(i:ℕ)(v:x∈ B' i) : bounded x B:=by
 induction i generalizing x with
 | zero=> obtain ⟨w,e,v,t⟩:=v; exact bounded_of_le (diced_le v) (h.ample _ e)
 | succ i ih=> obtain ⟨y,u,e⟩:= graft h _ v; exact bounded_of_le e.1 (ih u)
lemma cards(i:ℕ)(v:x∈ B' i) : x.dim+i=4:=by
 induction i generalizing x with
 | zero=> obtain ⟨w,e,v,t⟩:=v; exact ((diced_plane v).dim.trans (h.top _ e))
 | succ i ih=> obtain ⟨w,⟨y,e,p⟩,v,t⟩:=v; rw [((diced_plane v).dim)]; have hp:= facet_dim p; have hv:= ih e; omega
lemma sess(i:ℕ)(e:x∈ B' i)(v:t.Tiny)(hx:t.boundary x) :∃ y∈ B' (i+1),y≤x ∧ t ≤ y:=by
 obtain ⟨w,t',p⟩:= facets_cover hx; obtain ⟨y,vA,hg,ht⟩:= coverage (L:={u|∃ y∈B' i,u.facet y}) r v p ⟨_,e,t'⟩; exact ⟨y,vA,ht.trans (proper t').1,hg⟩
lemma setEq (i:ℕ)(e:x∈B' i)(v:y∈B' i)(p:t ≤ x)(q:t.inside y):x=y:=by
 let u:= cards h _ e; apply Eq.symm; cases i with
 | zero=> exact separate (r:=r) (fun x e y v=>h.localOrder x y (h.ample _ e) (h.ample _ v)) h.top v e q p
 | succ i=>
   apply separate (L:={u|∃ y∈ batch r L i,u.facet y}) (r:=r) (N:=x.dim) _ _ v e q p
   · rintro x ⟨x',p,e⟩ y ⟨y',q,v⟩
     exact h.localOrder x y (bounded_of_le (proper e).1 (shoulder h i p)) (bounded_of_le (proper v).1 (shoulder h i q))
   rintro x' ⟨t',p,e⟩; have h1:= cards h _ p; have h2:=facet_dim e; omega
-- Refinement cross-rank: If T is interior of higher rank, cannot lie in smaller one closed.
lemma flatCap (i j:ℕ)(e:x∈ B' i)(a:y∈ B' (i+j+1))(v:t ≤ y)(p:t ≤ x): boundary t x:=by
 refine ⟨p,fun q=>?_⟩
 induction j generalizing y with
 | zero=> obtain ⟨Y,hp,hV⟩:= graft h _ a; have r:= setEq h i hp e (v.trans hV.1) q; exact hV.2 (inside_lift (r.symm ▸ q) v hV.1)
 | succ j ih=> obtain ⟨Y,p,V⟩:= graft h (i+j+1) a; exact ih p (v.trans V.1)
lemma faceCut(i:ℕ)(e:x∈ B' i)(a:y∈ B' (i+1))(v:t.inside y)(ht:t≤x) : y.boundary x:=by
 let q:= flatCap h i 0 e a (place v) ht; obtain ⟨w,p,V⟩:= facets_cover q; obtain ⟨Y,u,s,k⟩:=a
 let hY:= dice_own s V (show w∈ {y|∃ z∈batch r L i,y.facet z} from ⟨_,e,p⟩) v
 exact boundary_mono (proper p) hY
lemma inheritB(i j:ℕ)(e:x∈ B' i)(a:y∈ B' (i+j+1))(u:t.Tiny)(v:t.inside y)(p:t ≤ x):boundary y x:=by
 induction j generalizing i x with
 | zero=> exact faceCut h i e a v p
 | succ j ih=>
   let q:= flatCap h _ _ e a (place v) p
   obtain ⟨Y,Z,p,t⟩:= sess h i e u q; exact lies_plane ((ih _ Z ((show i+j.succ+1=i+1+j+1 by omega) ▸ a) t).1.trans p) v q
structure Story (x:Rooms): Prop where
 floor : Tiny x
 single :∃ i≤4,∃ k∈B' i,x.inside k
lemma slice(x:Rooms)(e:x.Tiny) {y} (a:x≤y) (i:ℕ)(r:y∈ B' i):∃ j≥i,∃ z∈B' j, x.inside z∧ z ≤ y:=by
 by_cases v:x.inside y
 · exact ⟨i,le_rfl,y,r,v,le_refl y⟩
 obtain ⟨z,p,u,a⟩:= sess h i r e ⟨a,v⟩; obtain ⟨j,H,Z,T,q,he⟩:= slice x e a (i+1) p; exact ⟨j,Nat.le_trans (by omega) H,Z,T,q,he.trans u⟩
termination_by 5-i
decreasing_by have t:= cards h _ r; omega
lemma tell (v:t.Tiny): Story (r:=r) (L:=L) t:=by
 obtain ⟨y,e,p⟩:= h.stand _ v; obtain ⟨x,A,p,q⟩:= coverage r v p e; obtain ⟨i,u,k,g,R,hK⟩:= slice h t v p 0 A; exact ⟨v,i,(by have h:= cards h _ g; omega),k,g,R⟩
lemma unique (t₁:t.Tiny)(i j:ℕ)(e:x∈ B' i)(a:y∈ B' j)(u:t.inside x)(v:t.inside y):x=y:=by
 rcases lt_trichotomy i j with h1|h1|h1
 · exact False.elim ((flatCap h i (j-i-1) e ((show j=i+(j-i-1)+1 by omega) ▸ a) (place v) (place u)).2 u)
 · subst j; exact setEq h _ e a (place u) v
 exact False.elim ((flatCap h j (i-j-1) a ((show i=j+(i-j-1)+1 by omega) ▸ e) (place u) (place v)).2 v)
def BlockQ (r:Rooms→ℕ)(L:Set Rooms)(n:ℕ)(x:Rooms): Prop := x∈ batch r L (4-n) ∧ x.dim=n

lemma rising (p:BlockQ r L x.dim x) (q:BlockQ r L y.dim y)(u:t.Tiny)(ht:t ≤ y)(v:t.inside x): x ≤ y:=by
 have he:= cards h _ p.1; have ha:= cards h _ q.1
 rcases slice h t u ht _ q.1 with ⟨j,u',z,v',hz,t⟩; rw [unique h u _ _ p.1 v' v hz]; exact t
lemma dim_no(p:x ≤ y): x.dim ≤ y.dim:=card_le_card (dim_le p)
lemma from_batch(i:ℕ)(u:x∈ B' i): BlockQ r L x.dim x:= ⟨(show i=4-x.dim by have t:= cards h _ u; omega) ▸ u,rfl⟩
lemma trunk01(p:x∈L)(u:t.Tiny)(v:t≤x):∃ y, BlockQ r L 4 y ∧ t ≤ y:=by obtain ⟨y,z,e,f⟩:= coverage r u v p; exact ⟨y,⟨z,by simpa using cards h 0 z⟩,e⟩
end Rooms
end YM.CF.VolumeCape

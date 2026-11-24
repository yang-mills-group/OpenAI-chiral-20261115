import YM.CF.Vp929.Law.Guided
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.VolumeCape
open Lattice Finset Function Metric Rooms Mos Mesa Cube Lat WalkBound Guide March
open scoped Topology Classical Matrix.Norms.Frobenius NNReal
namespace Palace

structure Pal where
 lots : Set Rooms
 rank: Rooms → ℕ
 showFrame : Rooms → March
variable (x:Pal)
structure Ready (C:Side)(B:ℕ)(x:Pal):Prop where
 roof:Canopy x.lots x.rank (B*C.val)
 wide: wetted C x.rank x.lots
namespace Pal
variable {A D:Realms}{p:Edge Cover}{g:Elm}{C:Side}{v:Rooms}{n i B:ℕ}{K:ℝ}
abbrev memQ (y:Rooms):=Knoll x.lots x.rank y
abbrev Pri(p:Edge Cover)(y:Rooms):= x.memQ y∧ Rooms.inside (zone p) y
abbrev replace (s:March)(v:Rooms)(A D:Realms)(p:Edge Cover)(C:Side)(K:ℝ):SU.E:= if wellF v A C 1 then A p else ((Pick s v K C D) p.1)⁻¹*Pick s v K C D (p.1+Lattice.step p.2)
def action (A D:Realms)(C:Side)(K:ℝ)(n:ℕ) : Realms:=fun p=> if h:∃ y, x.Pri p y ∧ y.dim=n then Pal.replace (x.showFrame h.choose) h.choose A D p C K else D p
lemma release_fail (v:¬∃ y, x.Pri p y∧ y.dim=n): x.action A D C K n p=D p:=dif_neg v
variable {x} (h:Ready C B x)
include h
lemma emerge(p:Edge Cover):∃ z,x.Pri p z:=by obtain ⟨j,v,t,p,e⟩:= (tell h.roof (span_fixed p.1 p.2)).single; exact ⟨t,from_batch h.roof _ p,e⟩
lemma unites {w:Rooms}(p₁:x.Pri p v)(p₂:x.Pri p w) : v=w:= unique h.roof (span_fixed p.1 p.2) _ _ p₁.1.1 p₂.1.1 p₁.2 p₂.2
lemma release (t:x.Pri p v)(vQ:v.dim=n) : x.action A D C K n p = Pal.replace (x.showFrame v) v A D p C K:=by
 have s:∃ y,x.Pri p y ∧ y.dim=n:=⟨_,t,vQ⟩; show _=_; rw [Pal.action,dif_pos s, unites h s.choose_spec.1 t]
omit h
protected def Guards (C:Side)(n:ℕ)(K:ℝ)(x:Pal)(A D:Realms):Prop:= (∀ y:Rooms,x.memQ y→wellF y A C 1→ Agrees y.marks A D)∧∀ y:Rooms,x.memQ y → y.dim<n→ wellF y D C K
variable (hG:Pal.Guards C n K x A D)
include h hG
lemma sane {K':ℝ}:∀ y:Rooms,x.memQ y→ wellF y A C 1→ Agrees y.marks A (x.action A D C K' n):=by
 intro y v w p a q; let t: zone p ≤ y:= spanFits.mpr ⟨a,q⟩; let g:= hG.1 y v w p a q; by_cases u:∃ z,x.Pri p z∧ z.dim=n; swap; · rw [release_fail x u,g]
 obtain ⟨z,u,wz⟩:=u; let f:=rising h.roof u.1 v (span_fixed p.1 p.2) t u.2; rw [release h u wz,Pal.replace,if_pos]; obtain ⟨x,t⟩:= w; exact ⟨x,Mos.Seal.low f t⟩

abbrev funds(B:ℕ)(K L:ℝ)(C:Side):Prop:=∀ (L':Set Rooms)(r:Rooms→ℕ), Canopy L' r (B*C.val) → wetted C r L' →∀ x,Knoll L' r x→∀ A:Realms,(∀ y,TrailX L' r y x→ wellF y A C K) →∃ v,Veil x A C v L
lemma bpaid {K':ℝ}(t:funds B K K' C)(p:1≤ K)(q:0≤K') : Pal.Guards C (n+1) (max K (K'+2)) x A (x.action A D C K' n):=by
 let Y:=x.action A D C K' n; have hs:(∀ y:Rooms,x.memQ y→wellF y A C 1→ Agrees y.marks A Y):= sane h hG; refine ⟨hs,fun y v e=> ?_⟩
 have A'(z:Rooms)(s:x.memQ z)(p':z.dim<n) : Agrees z.marks D Y:= by
    intro i w Z; symm; refine release_fail x (fun V=>?_); obtain ⟨y,t,H⟩:=V; have he:= rising h.roof t.1 s (span_fixed i.1 i.2) (spanFits.2 (And.intro w Z)) t.2; exact (Rooms.dim_no h.roof he).not_gt (lt_of_lt_of_le p' H.ge)
 by_cases i:y.dim<n
 · obtain ⟨z,l⟩:= Guide.well_room (A' y v i) (hG.2 y v i); exact ⟨z,l.up (le_max_left ..)⟩
 have i:y.dim=n:=(by omega); by_cases z:wellF y A C 1; · obtain ⟨Q,l⟩:= Guide.well_room (hs y v z) z; exact ⟨Q,l.up (le_trans p (le_max_left ..))⟩
 let Q:= Pick (x.showFrame y) y K' C D; have H:Veil y D C Q (K'+2):= Guide.upper _ (t _ _ h.roof h.wide y v D (fun l E=>hG.2 _ E.1 (E.2.2.1.trans_eq i)))
 suffices vv:Seal y Y C Q (K'+2) from ⟨Q,vv.up (le_max_right ..)⟩; intro a j u; by_cases V:Rooms.inside (zone (a,j)) y
 · change GDist (Q a*x.action A D C K' n (a,j)) _ ≤ _; rw [release h ⟨v,V⟩ i, Pal.replace,if_neg z, show Pick _ _ _ _ _ = Q from rfl, mul_inv_cancel_left]; unfold GDist; rw [dist_self]; positivity
 obtain ⟨z,w,t⟩:=reflex h.roof (zone (a,j)) (span_fixed a j) ⟨u,V⟩ v; let Qk:= place t; have h:= H a j ⟨u,V⟩; rw [← (A' z w.1 (w.2.2.1.trans_eq i)) (a,j) (spanFits.mp Qk).1 (spanFits.mp Qk).2]; exact h
end Pal
end Palace
end YM.CF.VolumeCape

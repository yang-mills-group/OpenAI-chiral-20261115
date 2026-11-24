import YM.CF.Vp929.Law.Cuboid
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.VolumeCape
open Lattice Finset Function
open scoped Classical
namespace Wall
variable {x y z:Wall}
lemma boundaryAxis (p:x ≤ y)(e:¬ x.cabin y): y.win∧ ∃ a,x=lone a ∧ y.tips a:=by
 refine ⟨by_contra fun t=>e ⟨p,fun v=>(t v).elim⟩,?_⟩
 have h:¬ x.win:=fun v=>e (cabin_win p v); unfold win at h; have ht:= x.e; have he: x.b=x.a:=by omega
 refine ⟨x.a, Wall.ext rfl he,by_contra fun q=>e ⟨p,fun v=>?_⟩⟩; unfold tips at q; push Not at q; obtain ⟨u,w⟩:= full p; omega
lemma boundaryOut (p:y.win)(e:y.tips x.a)(h:¬x.win): ¬ x.cabin y:=by intro q; obtain ⟨i,j⟩:= q.2 p; unfold tips at e; unfold win at h; omega
protected lemma Tiny.eq {x y:Wall}(e:x ≤ y)(v:x.win)(t:Tiny y):x=y:=by obtain ⟨a,b⟩:= full e; apply Wall.ext <;> unfold Tiny win at * <;> omega
end Wall
namespace Rooms
variable {x y z v:Rooms} {a b:Cover}
abbrev boundary(x y:Rooms):Prop:= x ≤ y ∧ ¬ inside x y
lemma bound_edge (p:boundary x y): ∃ i:Axis,(y i).win ∧∃ a,x i=Wall.lone a ∧ (y i).tips a:=by
 obtain ⟨v,w⟩:= p; unfold inside at w; push Not at w; obtain ⟨i,w⟩:=w; exact ⟨i,Wall.boundaryAxis (v i) w⟩
lemma boundary_mono (p:x.boundary y)(q:z≤x): z.boundary y:= ⟨q.trans p.1,fun e=> p.2 (inside_lift e q p.1)⟩
def facet (x y:Rooms):Prop:= ∃ i∈y.doors,∃ a,(y i).tips a ∧ x=Function.update y i (Wall.lone a)
lemma facet_yes(i:Axis)(p:i∈x.doors)(v:ℤ)(q:(x i).tips v): boundary (update x i (Wall.lone v)) x:= by
 refine ⟨fun j=>?_,?_⟩
 · by_cases t:j=i; subst j; rw [Function.update_self]; exact Wall.tipBox q
   rw [Function.update_of_ne t]
 intro z; let g:= z i; rw [Function.update_self] at g; exact Wall.boundaryOut (intro_door.1 p) q (lt_irrefl _) g
lemma proper (p:x.facet y):boundary x y:=by obtain ⟨i,h,v,p,rfl⟩:=p; exact facet_yes i h v p
lemma facet_dim (p:x.facet y): y.dim=x.dim+1:= by
 obtain ⟨i,h,K,hK,rfl⟩:=p; let x:Rooms:= Function.update y i (Wall.lone K); change _=x.doors.card+1
 have g:x.doors= y.doors.erase i:=by
    ext j; rw [intro_door,Finset.mem_erase]; by_cases h:j=i
    · subst j; simp [x,Wall.win,Wall.lone]
    rw [and_iff_right h]; simp [x,h,intro_door]
 unfold dim; rw [g,card_erase_add_one h]
lemma facets_cover (p:x.boundary y): ∃ z,z.facet y ∧ x≤z:=by
 obtain ⟨i,v,a,h,q⟩:= bound_edge p; refine ⟨_,⟨i,intro_door.2 v,a,q,rfl⟩,fun j=>?_⟩; by_cases t:j=i; subst j; rw [Function.update_self,h]
 rw [Function.update_of_ne t]; exact p.1 j
-- nonvacancy interior
lemma tiny_at (x:Rooms):∃ y,y.Tiny ∧ y≤x ∧ y.Plane x:=by obtain ⟨y,k,_,t,w⟩:=pad x (here_tiny _) x.foot_in; exact ⟨y,k,t,w⟩

lemma lies_plane (h:x≤y)(t:z.inside x)(v:z.boundary y): x.boundary y:=by
 obtain ⟨i,u,a,f,r⟩:= bound_edge v; have hh:= t i; rw [f] at hh; let l:= h i; have hv: ¬ (x i).win:=by
    intro q; obtain ⟨e,w⟩:= hh.2 q; have he:= Wall.full l; change (y i).a=a ∨ (y i).b=a at r; change _ < _ at q; change a < _ at e; change _<a at w; omega
 have he:= Wall.stay hv hh.1; exact ⟨h,fun h=> by have t:= h i; rw [←he] at t; exact v.2 (fun j=>by

    have hz: ¬ (Wall.lone a).cabin (y i):= Wall.boundaryOut u r (lt_irrefl _); exact (hz t).elim)⟩
end Rooms
end YM.CF.VolumeCape

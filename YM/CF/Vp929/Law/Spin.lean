import YM.CF.Vp929.Law.Motion
import YM.CF.Vp929.Law.Parch
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.CF.VolumeCape
open Lattice Finset Function Rooms Wall
open scoped Classical
namespace March
variable (x:March) (a b v:Rooms) {L K:Set Rooms} {r r₁:Rooms→ℕ}
local notation "P"=> x.step.perm
private theorem spinning (p:Rooms.Plane a b): Plane (x.follow a) (x.follow b):= by
 have h(i): (x.follow a (x.step.perm i)).win ↔ (x.follow b (P i)).win:= by rw [stride,stride,swing_win,swing_win]; exact p.win i
 refine ⟨Finset.ext fun i=>?_,fun i=>?_⟩ <;> obtain ⟨i,rfl⟩:= x.step.perm.surjective i
 · rw [intro_door,intro_door,h]
 rw [x.stride,x.stride,x.swing_win]; intro u; rw [p.2 _ u]
@[simp] theorem rotation : Plane (x.follow a) (x.follow b) ↔ Plane a b:= ⟨fun p=> by simpa using spinning x⁻¹ _ _ p,spinning x a b⟩
lemma ceilings : doors (x.follow a)=(doors a).map x.step.perm.toEmbedding:=by
 ext i; obtain ⟨i,rfl⟩:= x.step.perm.surjective i; rw [mem_map_equiv, intro_door,stride,swing_win]; simp [intro_door]
lemma shallow : (x.follow a).dim=a.dim:=by unfold dim; rw [ceilings,card_map]
lemma cabin2(i:Axis)(a b:Wall)(t: Wall.cabin a b): Wall.cabin (x.swing i a) (x.swing i b):=by
 refine ⟨(swing_le x i a b).2 t.1, fun p=>?_⟩; obtain ⟨u,v⟩:= t.2 ((swing_win x i b).1 p); unfold swing; split <;> simp only [drift,reverse] <;> omega
private lemma in_spin(p:inside a b) : inside (x.follow a) (x.follow b):=by intro i; obtain ⟨i,rfl⟩:=x.step.perm.surjective i; rw [x.stride,x.stride]; exact cabin2 x _ _ _ (p _)
lemma isInside : inside (x.follow a) (x.follow b) ↔inside a b:=⟨fun p=>by simpa using in_spin x⁻¹ _ _ p, in_spin x a b⟩
lemma meet(p:meets a b): meets (x.follow a) (x.follow b):=by obtain ⟨c,h,v⟩:=p; exact touch ((stride_le ..).2 h) ((stride_le ..).2 v)
lemma raise (f:Wall)(i:Axis) : x.follow (update a i f)=update (x.follow a) (x.step.perm i) (x.swing i f):=by funext j; obtain ⟨j,rfl⟩:= x.step.perm.surjective j; by_cases h:i=j; subst i; simp; rw [Function.update_of_ne (mt (x.step.perm.injective.eq_iff).mp (Ne.symm h)),stride,stride,Function.update_of_ne (Ne.symm h)]
private lemma facers (p:a.facet b): Rooms.facet (x.follow a) (x.follow b):=by
 obtain ⟨i,v,w,e,rfl⟩:=p; refine ⟨P i,by rw [intro_door,stride,swing_win]; exact intro_door.1 v, x.push i w, (by rw [stride]; exact (x.swing_tips _ _ _).2 e),?_⟩; rw [x.raise]; unfold swing March.push; split <;> rfl
lemma facets_eq : Rooms.facet (x.follow a) (x.follow b) ↔ a.facet b:= ⟨fun h=>by simpa using facers x⁻¹ _ _ h,facers x a b⟩
lemma passport (i:Axis):Function.Surjective (x.push i):= by
 intro z; unfold March.push; by_cases v:x.step.flip i=true; exact ⟨x.endpt (x.step.perm i)-z,by simp [v]⟩; exact ⟨z-x.endpt (x.step.perm i),by simp [v]⟩
variable {x a b}
def turnClan (x:March)(L K:Set Rooms):Prop:=∀ a, a∈L ↔ x.follow a∈K
protected lemma turnClan.rev (v:turnClan x L K): turnClan x⁻¹ K L:=fun i=> by have p:=v (x⁻¹.follow i); simpa using p.symm
lemma stepPush (x:March)(i:Axis)(z:ℤ) : x⁻¹.push (x.step.perm i) (x.push i z)=z:=by
 let a:Cover:= fun _=>z; have h:=congrFun (x.left a) i; have p(j:March)(i:Axis)(z:Cover):j.slide z (j.step.perm i)=j.push i (z i):= j.footstep z i
 rw [←p x i a]; change _=a i; rw [←p]; change x⁻¹.slide (x.slide a)  (x.step.perm.symm (x.step.perm i))=_; simpa only [Equiv.symm_apply_apply] using h
private lemma cut_face (p:turnClan x L K)(i:Axis)(v:ℤ)(e:v∈Cuts L a i): x.push i v∈ Cuts K (x.follow a) (x.step.perm i):=by obtain ⟨y,q,u,k⟩:=e; refine ⟨x.follow y,(p y).1 q, x.meet _ _ u,?_⟩; rw [x.stride]; exact (x.swing_tips ..).2 k
private lemma cutBack (p:turnClan x L K)(i:Axis)(v:ℤ)(e: x.push i v∈ Cuts K (x.follow a) (x.step.perm i)) : v∈Cuts L a i :=by obtain q:=cut_face p.rev (x.step.perm i) _ e; rw [stepPush,foll_left] at q; change v∈Cuts L a (x.step.perm.symm (x.step.perm i)) at q; simpa using q
private lemma dicedFaces (p:turnClan x L K)(q: diced L a b): diced K (x.follow a) (x.follow b):=by
 intro i; obtain ⟨i,rfl⟩:=x.step.perm.surjective i; let w:= (x.follow a) (P i); let e:=q i
 refine ⟨((x.stride_le a b).2 (diced_le q)) _, ((spinning x a b (diced_plane q)).win _).2, ?_,?_,?_ ⟩
 · have t:= cut_face p i _ e.low; have k:= cut_face p i _ e.high; rw [stride]; unfold March.push at t k; unfold swing; by_cases h:x.step.flip i=true <;> simp only [h,if_false,if_true,not_false_eq_true] at t k ⊢ <;> first|exact t|exact k
 · have t:= cut_face p i _ e.low; have k:= cut_face p i _ e.high; rw [stride]; unfold March.push at t k; unfold swing; by_cases h:x.step.flip i=true <;> simp only [h,if_false,if_true,not_false_eq_true] at t k ⊢ <;> first|exact t|exact k
 intro a' t; obtain ⟨j,rfl⟩:= passport x i a'; obtain h:=e.apart j (cutBack p _ _ t); rw [stride]; unfold swing March.push; split <;> simp only [reverse,drift] <;> omega
lemma spin_spans (p:turnClan x L K) (s:∀ i,r i=r₁ (x.follow i)) : turnClan x (Spread r L) (Spread r₁ K):= by
 have h{r r' : Rooms→ℕ}{x:March}{L K:Set Rooms} (p:turnClan x L K)(s:∀ i,r i=r' (x.follow i)) {a:Rooms}(v:a∈Spread r L):x.follow a∈ Spread r' K:= by
    obtain ⟨y,v,t,l⟩:=v; refine ⟨_, (p y).1 v,dicedFaces p t,?_⟩; intro z hz Z W; obtain ⟨i,rfl⟩:= x.fnQ.surjective z; exact s i ▸ (s y ▸ l i ((p i).2 hz) ((x.isInside a _).1 Z) ((x.rotation y i).1 W))
 intro a; constructor; exact h p s; intro a'; have v:= h p.rev (r:=r₁) (r':=r) (fun i=> by rw [s]; simp) a'; simpa using v
lemma spinBatch (p:turnClan x L K) (s:∀ i,r i=r₁ (x.follow i)) (n:ℕ) : turnClan x (batch r L n) (batch r₁ K n):=by
 induction n with
 | zero=> exact spin_spans p s
 | succ n ih =>
   apply spin_spans _ s; intro a; constructor
   · rintro ⟨b,v,h⟩; exact ⟨x.follow b,(ih b).1 v,(x.facets_eq ..).2 h⟩
   rintro ⟨b,v,u⟩; obtain ⟨b,rfl⟩:= x.fnQ.surjective b; exact ⟨b,(ih b).2 v,(x.facets_eq ..).1 u⟩
end March
end YM.CF.VolumeCape

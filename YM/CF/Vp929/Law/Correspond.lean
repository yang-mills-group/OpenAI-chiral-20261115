import YM.CF.Vp929.Law.Ignite
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.VolumeCape
open Lattice Finset Function Metric Rooms Mos Mesa Cube Lat WalkBound Guide March Spire
open scoped Topology Classical Matrix.Norms.Frobenius NNReal
namespace Palace
namespace Pal

variable {x y:Pal} {A D:Realms}{p:Edge Cover}{g:Elm}{C:Side}{v:Rooms}{n i B:ℕ}{K:ℝ}
def Twist (x y:Pal)(s:March)(R:ℕ):Prop:= March.turnClan s x.lots y.lots ∧ (∀ z,x.rank z=y.rank (s.follow z)) ∧ ∀ z:Rooms,z.bounded R→ y.showFrame (s.follow z)=s*x.showFrame z
variable (s:March) (h:Twist x y s (B*C.val)) (r:Ready C B x) (t:Ready C B y)
include h
lemma twists_mem (v:Rooms): x.memQ v ↔ y.memQ (s.follow v):=by
 let k:=spinBatch h.1 h.2.1 (4-v.dim); unfold memQ Knoll Rooms.BlockQ; rw [s.shallow]; exact and_congr (k v) Iff.rfl
include r t
omit h r t in
private lemma beam (s:Step)(g:Elm)(A:Realms)(v:Rooms)(F:March)(C:Side)(K:ℝ) (D:Realms)(a:Cover) : s.read (fun p:Edge Cover=> Pal.replace F v A D p C K) a = if wellF v A C 1 then s.read A a else (Pick F v K C D a)⁻¹*Pick F v K C D (a+s.vec):=by
 unfold Step.read; by_cases p:wellF v A C 1
 · cases s.neg <;> simp [Pal.replace,p]
 split; · rename_i h; simp only [Pal.replace,Step.used,h,↓reduceIte,p]; simp [Step.vec,h,sub_eq_add_neg]
 rename_i h; simp [Pal.replace,Step.used,h,p,Step.vec]
omit h r t in
private lemma read_at {V F:Realms}(a:Cover)(e:Step)(v:V (e.used a)=F (e.used a)):e.read V a=e.read F a:=by unfold Step.read; rw [v]
protected lemma clockwise(K:ℝ)(n:ℕ)(A D:Realms): x.action (turns s A) (turns s D) C K n=s.turns (y.action A D C K n) :=by
 funext p; rcases p with ⟨a,i⟩; let g₀:=posDir i; let X:= (a,i); let z:= s.lane g₀ a; obtain ⟨v₀,H⟩:= emerge r X; have U:= twists_mem s h v₀; let F:=x.showFrame v₀; let Y:=s.follow v₀
 have j:y.Pri z Y:=⟨U.1 H.1,(by unfold z; rw [March.lane_z]; exact (s.isInside ..).2 H.2)⟩; let v:=g₀.rotate s.step; have tv:=h.2.2 v₀ (shoulder r.roof _ H.1.1); have c:s.slide a+v.vec=s.slide (a+Lattice.step i):=(s.next_point g₀ a).symm
 change x.action (s.turns A) (s.turns D) C K n X= g₀.read (s.turns (y.action A D C K n)) a; rw [ladder]; by_cases p:v₀.dim=n
 · rw [release r H p,read_at (F:=fun k=> Pal.replace (y.showFrame Y) Y A D k C K) (s.slide a) v (show y.action A D C K n z= (fun k=> Pal.replace (y.showFrame Y) Y A D k C K) z from release t j ((s.shallow ..).trans p)), beam v 1]; unfold Pal.replace
   split_ifs with d d' q;
   · exact ladder s A a g₀
   · exact (d' ((wellQuote ..).2 d)).elim
   · exact (d ((wellQuote ..).1 q)).elim
   change _ = Spire.polarT s.charge _; change y.showFrame Y=s*F at tv; rw [tv]; rw [Guide.rateTurn s F]; unfold kicks; rw [c,map_mul,map_inv]
 have ht0(Y:Rooms):y.Pri z Y → Y.dim≠n :=fun u=> (unites t j u) ▸ (fun w=>(p ((s.shallow ..).symm.trans w)))
 let x' := x.action (s.turns A) (s.turns D); rw [release_fail x (fun ⟨u,v,k⟩=>p ((congrArg dim (unites r H v)).trans k)),read_at _ v (release_fail y (fun ⟨u,k,e⟩=> ht0 u k e))]; exact s.ladder D a g₀
end Pal
end Palace
end YM.CF.VolumeCape

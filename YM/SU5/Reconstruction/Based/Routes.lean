import YM.Lattice.Path
import YM.Lattice.Box
/- # Physically connected Wilson paths in a local support, even if S disconnected. -/

set_option autoImplicit false
noncomputable section
namespace YM.Lattice.WalkRoots
open Function Set
variable {S R : Finset Cover}{x y z:Cover}{p q:Walk}

/- Design: `ReachesBy S x y p` is on cover. Actual period machines later will use it only
at that height; components & gauge bases may be quite different after advancing from it. -/
def Joins(S:Finset Cover)(x y:Cover)(p:Walk):Prop := stop x p=y ∧ ∀ z∈ visits x p,z∈ S
def Meets(S:Finset Cover)(x y:Cover):Prop := ∃ p,Joins S x y p

namespace Joins
lemma nil (h:x∈ S):Joins S x x []:=⟨rfl,by simpa [visits] using h⟩
lemma fst (h:Joins S x y p):x∈ S:=h.2 x (by cases p <;> simp [visits])
lemma oneDown (h:x∈S) (d:Step) (g:x+d.vec∈ S): Joins S x (x+d.vec) [d]:=⟨rfl,by simp [visits,h,g]⟩
lemma cons (h:x∈S)(d:Step)(g:Joins S (x+d.vec) y p): Joins S x y (d::p):=
  ⟨g.1,fun z hz=> (List.mem_cons.mp hz).elim (fun e=>e.symm ▸ h) (g.2 _)⟩
lemma tailJoin (d:Step) (h:Joins S x y (d::p)): Joins S (x+d.vec) y p:= ⟨h.1, fun z hz=> h.2 _ (List.mem_cons_of_mem _ hz)⟩
lemma paste (h:Joins S x y p)(u:Joins S y z q): Joins S x z (p++q):=by
 induction p generalizing x with
 | nil => rw [(show x=y from h.1),List.nil_append]; exact u
 | cons d p ih=> exact cons h.fst d (ih (tailJoin d h))
lemma turn (h:Joins S x y p): Joins S y x (reverse p):=by
 induction p generalizing x with
 | nil => exact (by have hv:x=y:=h.1; subst y; exact h)
 | cons d p ih=>
    let t:Cover:= x+d.vec
    have e:t+d.rev.vec=x:=by unfold t; rw [Step.vec_rev]; abel
    have hz: t+d.rev.vec ∈ S := e.symm ▸ h.fst
    have p':Joins S t y p:= tailJoin d h
    rw [reverse,List.reverse_cons,List.map_append]
    exact paste (ih p') (by exact (congrArg (Joins S t · [d.rev]) e).mp (oneDown p'.fst d.rev hz))
lemma snd (h:Joins S x y p):y∈ S:= h.turn.fst
lemma more (u:S⊆R)(h:Joins S x y p):Joins R x y p:= ⟨h.1,fun z hz=> u (h.2 z hz)⟩
end Joins

namespace Meets
lemma refl (h:x∈ S): Meets S x x:=⟨[],Joins.nil h⟩
lemma trans (h:Meets S x y)(u:Meets S y z):Meets S x z:= ⟨_, h.choose_spec.paste u.choose_spec⟩
lemma symm (h:Meets S x y): Meets S y x:= ⟨_, h.choose_spec.turn⟩
lemma stepLink (d:Step)(hx:x∈ S)(hy:x+d.vec∈ S):Meets S x (x+d.vec):=⟨[d],Joins.oneDown hx d hy⟩
lemma fst (h:Meets S x y):x∈S:= h.choose_spec.fst
lemma snd (h:Meets S x y):y∈S:= h.choose_spec.snd
end Meets

/-- Wilson plan. Require root at a vertex of each component. Keep path of root itself trivial.
No need to require paths form a tree. -/
structure RouteMap(S:Finset Cover) where
 base : Cover → Cover
 path : Cover → Walk
 toSite (x:Cover) : x∈S → Joins S (base x) x (path x)
 same {x y:Cover} : Meets S x y → base x=base y
 path_self {x:Cover} : x∈ S→ base x=x→path x=[]
namespace RouteMap
variable (G:RouteMap S)
lemma base_mem(x:Cover)(h:x∈S):G.base x∈ S:=(G.toSite x h).fst
lemma stays (x:Cover)(h:x∈S):G.base (G.base x)=G.base x:= G.same ⟨_,G.toSite x h⟩
lemma edge (x:Cover)(i:Axis)(h:x∈S)(g:x+step i∈ S):G.base x=G.base (x+step i):=
 G.same (Meets.stepLink (posDir i) h g)
end RouteMap

section choice
open Classical
lemma root_Plan (f:Cover→Cover)(a:∀x∈ S, Meets S (f x) x)(e:∀x y:Cover,Meets S x y→ f x=f y):
    ∃ M:RouteMap S,M.base=f:=by
 let P(x:Cover) := if h:x∈S ∧ f x≠x then (a x h.1).choose else []
 refine ⟨⟨f,P,fun x h=>?_, fun {x y}=>e x y,fun {x} _ h=>by simp [P,h]⟩,rfl⟩; by_cases g:f x=x
 · simpa [P,g] using Joins.nil h
 unfold P; rw [dif_pos ⟨h,g⟩]; exact (a x h).choose_spec
lemma routes_any(S:Finset Cover): Nonempty (RouteMap S):=by
 let C(x:↥S) := {v:Cover|Meets S v x.val}
 have p(x:↥S):(C x).Nonempty:= ⟨x,Meets.refl x.property⟩
 let u(x:Cover): Cover:= if h:x∈ S then (p ⟨x,h⟩).choose else x
 have he(x)(h:x∈S):Meets S (u x) x:=by rw [show u x =_ from dif_pos h]; exact (p ⟨x,h⟩).choose_spec
 have hw(x y:Cover)(h:Meets S x y):u x=u y:=by
    dsimp only [u]; rw [dif_pos h.fst,dif_pos h.snd]; have e:C ⟨x,h.fst⟩=C ⟨y,h.snd⟩:= Set.ext fun z=> (show Meets S z x ↔ Meets S z y from ⟨fun g=>g.trans h,fun g=>g.trans h.symm⟩)
    exact (by
      -- choices for extension-point
      -- use congrArg on selector
      let sel (R:{T:Set Cover // T.Nonempty}):=R.property.choose
      exact congrArg sel (Subtype.ext e : (⟨_,p ⟨x,h.fst⟩⟩:{T:Set Cover // T.Nonempty})=⟨_,p ⟨y,h.snd⟩⟩))
 exact ⟨(root_Plan u he hw).choose⟩
lemma fixed_root (h:∀ y∈ S, Meets S x y): ∃ M:RouteMap S, ∀ y:Cover,M.base y=x:=by
 obtain ⟨M,t⟩:=root_Plan (fun _=>x) h (fun _ _ _=>rfl); exact ⟨M, fun i=> congrFun t i⟩
end choice
end YM.Lattice.WalkRoots

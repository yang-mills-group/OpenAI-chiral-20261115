import YM.SU5.Reconstruction.Marque.Angle
set_option autoImplicit false
noncomputable section
namespace YM.Marque.Flow
open Function Set Filter Metric NormedSpace ContinuousLinearMap BridgeClub CrossedFrame
open scoped ComplexOrder InnerProductSpace BigOperators Topology Classical
variable {H:Hilbert} (F:Bool) (g:Two) (N : Set E4 → Net H) (S:OS.Semigroup H clock) (Ω:H)
local notation "W"=> Wander H.space
local notation "ρ"=>Motion
local notation "U"=> Picket.trans S
noncomputable def roller : E4≃ₜ E4:= if F then (Lens g).toHomeomorph.trans (Homeomorph.neg E4) else (Lens g).toHomeomorph
@[simp] lemma forwards (p:E4):roller false g p=ρ g p:=rfl
@[simp] lemma away (p:E4):roller true g p= -ρ g p:=rfl
lemma mot {a b:Bool}(g h:Two)(x:E4): roller (a^^b) (g*h) x= roller a g (roller b h x):=by cases a <;> cases b <;> simp
lemma roller_one(x:E4):roller false 1 x=x:=by simp
lemma roller_inv(x:E4):roller F g⁻¹ (roller F g x)=x:=by cases F <;> simp
lemma roller_exit(x:E4):roller F g (roller F g⁻¹ x)=x:=by cases F<;> simp
lemma backlot(X:Set E4):roller F g '' (roller F g⁻¹ '' X)=X:=by rw[Set.image_image,show (fun x=>roller F g (roller F g⁻¹ x))=id from funext (roller_exit F g),Set.image_id]
structure Lot (b: Bool)(g:Two)(v:W): Prop where
   fleet:Fleet v b
   pecan:v Ω=Ω
   wagon (x:E4): Across v (U x) (U (roller b g x))
   ready (V:Set E4) : IsOpen V→ Conveys v (N V) (N (roller b g '' V))
local notation "L"=> Lot N S Ω -- order ?

namespace Lot
variable {N S Ω}
variable {p q:Bool}{s t:Two}{u v: Wander H.space}
lemma origin : Lot N S Ω false 1 1:= ⟨Fleet.one,rfl,fun i=> by simp only [roller_one]; exact Across.goesOne, fun V h=> by rw [show roller false 1 '' V= V from (by rw [show (roller false 1:E4→E4) = id from funext roller_one,image_id])]; exact Conveys.first _⟩ -- tune
lemma bezel0 : Lot N S Ω false bezel 1:=by
 have hx:(roller false bezel:E4→E4)=roller false 1:= funext (fun i=>by simp)
 refine ⟨Fleet.one,rfl,fun i=> ?_, fun V o=> ?_⟩
 rw [congrFun hx i]; exact (origin (S:=S) (N:=N) (Ω:=Ω)).wagon i
 rw [hx]; exact (origin (S:=S) (N:=N) (Ω:=Ω)).ready V o
variable (e:Lot N S Ω p s u)(h:Lot N S Ω q t v)
include e
lemma back:Lot N S Ω p s⁻¹ u⁻¹:= by
 refine ⟨e.fleet.inv,(show u⁻¹ Ω=Ω from u.injective (by rw [wander_back,e.pecan])), fun x=> ?_,fun V w=>?_⟩
 have hx:= (e.wagon (roller p s⁻¹ x)).inv; rwa [roller_exit] at hx
 have hv := (e.ready (roller p s⁻¹ '' V) ((roller p s⁻¹).isOpenMap V w)).back; rwa [backlot] at hv
include h
lemma times : Lot N S Ω (p^^q) (s*t) (u*v):= by
 refine ⟨h.fleet.times e.fleet,(show u (v Ω)= Ω from (by rw[h.pecan,e.pecan])),fun x=>?_,fun V w=>?_⟩
 · rw [mot]; exact Across.functor (h.wagon x) (e.wagon _)
 rw [show roller _ _ '' V= roller p s '' (roller q t '' V) from ?_]; exact Conveys.joins (h.ready V w) (e.ready _ ((roller q t).isOpenMap V w)) h.fleet -- universe placeholder
 rw [Set.image_image,show (roller (p^^q) (s*t):E4→ E4)=(fun x=> roller p s (roller q t x)) from funext (mot s t)]
end Lot
variable {Ω} {u v: Wander H.space}
-- pure property Mat
abbrev Able(u:W):Prop:= ∀ v:W,L false 1 v→ Commute v u
structure News(b:Bool)(g:Two)(u:W): Prop extends Lot N S Ω b g u where
   vert: Able N S (Ω:=Ω) u -- maybe Ω implicit

namespace News
variable {N S} {a b:Bool} {s t:Two}
lemma vacuumEstimate:News (Ω:=Ω) N S false 1 1:= { Lot.origin with vert:= fun _ _=>Commute.one_right _ } -- Prop proof constructor?
lemma bez:News (Ω:=Ω) N S false bezel 1:=⟨Lot.bezel0,fun _ _=>Commute.one_right _⟩
variable (p:News (Ω:=Ω) N S a s u) (q:News (Ω:=Ω) N S b t v)
include p
lemma inverse:News (Ω:=Ω) N S a s⁻¹ u⁻¹:= ⟨p.toLot.back,fun x w=> (p.vert x w).inv_right⟩
include q
lemma compose: News (Ω:=Ω) N S (a^^b) (s*t) (u*v):= ⟨p.toLot.times q.toLot, fun x w=>(p.vert x w).mul_right (q.vert x w)⟩
end News
variable (Ω)
noncomputable def Projector : Passage H.space where
 ok g:= {x|News (Ω:=Ω) N S false g x}
 pass:= News.vacuumEstimate
 plus {i j x y} b p:= News.compose (a:=false) (b:=false) b p
 opp {i x} p:=News.inverse p
local notation "κ"=>Projector N S Ω
lemma permit (g:Two) (v:W): v∈ (κ).ok g ↔ News (Ω:=Ω) N S false g v:= Iff.rfl
lemma allSpokes : (κ).spokes:= fun {i} u b v p=>(show News (Ω:=Ω) N S false i v from p).vert u ((show News (Ω:=Ω) N S false 1 u from b).toLot)
end YM.Marque.Flow

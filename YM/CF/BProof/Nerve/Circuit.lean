import YM.CF.BProof.Nerve.Era
/-! Use weighted Voronoi gaps instead of Delaunay lemma. This surrogate has
 dimension-4 *abstract simplices of barycentric weights*, used only in making
 the Basic maps. No eta' for other distances needed: can use any MinAbs tie lift beyond.
-/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4800
set_option maxHeartbeats 780000
noncomputable section
namespace YM.CF.BProof.Mesh.Nerve
open Lattice Function Finset Equiv Regard Rows Sleet
open scoped BigOperators Classical
variable {n:Side}{C A:Type*}{s z l k R d:ℕ}
namespace Carpet
open Guard Policy Sleet Pie
variable {U : Field n A Prop}{g:Field n A (Fin z)}
-- waivers may recycle irregular bills s.Look. expose `Barn` with U fields free. arbitrary lift later. Include ties in law transform, jitter derived.
abbrev plain(U:Field n A Prop)(g:Field n A (Fin z))(s:ℕ) :=stageD U g s z
local notation "Xκ"=>Site n
local notation "Ωκ"=> plain U g s
local notation "Υ"=> supporters U Ωκ s z
local notation "ακ"=> cent s z U Ωκ
local notation "Yκ"=>Joint U g
structure Note (U:Field n A Prop)(g:Field n A (Fin z))(s:ℕ)(a:ℝ) : Prop where
 he:0<s
 hp:SmallN s n
 perc:Spotty U s (cover s)
 flag:Busy.goodHue U g (King*s)
 small:2*press s<alpha z
 head:rate s z< a
-- might not need FClass Palette as explicit def.Const. No ℒ later cost.Price
variable {a:ℝ}(t:Note U g s a)
include t
lemma calm : Birthday s U (plain U g s):=by
 intro w; refine ⟨fun x u=>?_,fun x=>?_⟩; · apply And.intro (valid (U:=U) (g:=g) x w (s:=s)).1; exact (valid (U:=U) (g:=g) x w (s:=s)).2.trans (cap_le ..)
 rw [bary_age,mul_assoc]; exact (t.perc w).2 x
namespace Note
lemma light: Lustre U Ωκ s z:=fun i j h=> bright j h t.flag
lemma matrix(w:A)(x:Site n):(∀ i,0≤ακ w x i) ∧ ∑ i,ακ w x i=1:= material_p (calm t) w x
lemma seam(w:A)(x i:Xκ): i∈ Υ w x ↔ ακ w x i≠0:= cent_self (calm t) w x i
lemma localMark(w:A)(x i:Xκ)(h:i∈ Υ w x): U w i ∧ i∈region n x (Halo*s):=by
 obtain ⟨u,h⟩:= bonds (calm t) t.he t.hp w x x i (by simp) z t.small h; exact ⟨u,(reg_in ..).2 (stick (calm t) t.he w x i u h).1⟩
lemma union_card(w:A)(x y:Site n)(h:separation x y≤1): (Υ w x∪Υ w y).card≤5:= quint (calm t) t.light t.small t.hp t.he w _ _ h
lemma mat_b(w:A)(x y:Xκ)(h:separation x y≤1)(i:Xκ):|ακ w x i-ακ w y i|≤ a:= (visit (calm t) t.light t.small t.hp t.he w _ _ h i).trans t.head.le
abbrev receipt (s z:ℕ):ℕ:= Halo*s+z*(King*s)
lemma price_μ : Uses (Joint U g) (cent s z U (plain U g s)) (receipt s z) := Uses.thenL (Uses.comm (Policy.dawn U g).1 (wage_eq U g s)) (used (calm t) t.he)
lemma sent(u:Signed)(x:Site n)(E: Perm A)(h:Transforms (facet u x) (Joint U g) E)(w:A)(v i:Xκ) : ακ (E w) v i=ακ w (facet u x v) (facet u x i):=cent_ride (calm t) t.he t.hp u x E ((Mesh.Loyal.meet (Policy.day U g).1 (noble U g s t.hp)) u x E h) w v i
-- support overlap distant bound
lemma close0(x y:Site n)(w:A)(h:separation x y≤1)(i j:Xκ)(u:i∈Υ w x∪Υ w y)(v:j∈Υ w x∪Υ w y):separation i j≤ 2*(Halo*s):=by
 let P(i:Xκ)(q:i∈Υ w x∪Υ w y): separation x i≤Halo*s:=by
    rcases mem_union.mp q with a|b; exact reg_in ..|>.1 (t.localMark w x i a).2; have he:=bonds (calm t) t.he t.hp w x y i h z t.small b; exact (stick (calm t) t.he w x i he.1 he.2).1
 refine (separation_triangle i x j).trans ?_; rw [two_mul,separation_comm i x]; exact Nat.add_le_add (P i u) (P j v)
end Note
omit t
-- geometric licence. Quant n uniform. Include for tools. Use *another radius k>=King* later for primary net? Palette avoids.Solution.
-- let BK symbolic at order estimates. King literal on mesh criterion on receipt. cash purchase at ANY BK≥King.
abbrev demands (K s:ℕ)(n:Side):Prop:= tollK s K ≤ n.val ∧ SmallN s n
def limit(K s:ℕ):ℕ:=tollK s K+4*((4*(King*s))+50)
lemma demand_full(K s:ℕ)(n:Side)(h:limit K s < n.val):demands K s n:=⟨le_trans (Nat.le_add_right ..) h.le,lt_of_le_of_lt (Nat.le_add_left ..) h⟩
lemma investment(K:ℕ)(pK:King≤K)(n:Side)(s:ℕ)(a:ℝ)(q:demands K s n)(p:0<s)(h:2*press s < Guard.alpha (partK K))(g:rate s (partK K) < a): Bill n s K (netW n s K) (colours n s K) ∧ Note (netW n s K) (colours n s K) s a :=by
 let V:=palette q.1 p; exact ⟨V,p,q.2,V.pack,fun w x y u v t L=> V.safe w x y u v t (L.trans (Nat.mul_le_mul_right _ pK)), h,g⟩
end Carpet
end YM.CF.BProof.Mesh.Nerve

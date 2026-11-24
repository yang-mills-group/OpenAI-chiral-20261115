import YM.CF.BProof.Radar.Cluster
/-! Alt bounding radius around k colors: up to 2 k l to pay diameter exposed. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.BProof.Mesh
open Lattice Function Finset Equiv Regard
open scoped BigOperators Classical
variable {C A:Type*}{n:Side}{l k r d:ℕ}
namespace Sleet
variable (f:Field n A Prop)
open Rows Cat Crop.Native
local notation "xθ"=> Site n
def bowl(w:Signed→A)(i:Site n):Prop:=∃ s:Signed,f (w s) (s⁻¹.act i)
lemma shelter(p:∀ x:Site n,Moves (Equiv.addLeft x) f): Sym (bowl f):=by
 intro s x; choose E h using fun t:Signed=>p ((s*t)⁻¹.act x); let V:= (Equiv.arrowCongr (Equiv.mulLeft s).symm (Equiv.refl A)).trans (Equiv.piCongrRight E); refine ⟨V,?_⟩; intro i y
 unfold bowl; apply propext; have he(t:Signed):f (V i t) (t⁻¹.act y)= f (i (s*t)) ((s*t)⁻¹.act (facet s x y)):=by
    rw [show V i t=E t (i (s*t)) from rfl,h t]; change f (i (s*t)) ((s*t)⁻¹.act x+t⁻¹.act y)=_; rw [facet_apply, Signed.act_add]; simp [_root_.mul_inv_rev, Signed.act_mul]
 constructor; rintro ⟨t,u⟩; exact ⟨s*t, he t ▸ u⟩; rintro ⟨t,u⟩; refine ⟨s⁻¹*t,?_⟩; rw [he]; simpa using u
lemma bowl_split(p: SplitK n f r): SplitK n (bowl f) r:=by
 let g(t:Signed) : Field n A Prop:=fun z x=> f z (t⁻¹.act x); let F: Field n (Signed→A) (Signed→Prop):=fun z x t=>g t (z t) x; have hu:Uses F (bowl f) 0:=by intro x y z p; apply propext; apply exists_congr; intro i; exact iff_of_eq (congrFun (p (halo_subset 0 _ (mem_singleton_self x))) i)
 simpa using hu.epoch (SplitK.array Signed g (fun s=> SplitK.bearing s⁻¹.actEquiv.toEquiv p (fun i j=> separation_signed i j s⁻¹)))
@[simp] lemma crowd_in(i:Site n)(t:A): i∈crowd f t↔ f t i:=by simp [crowd]
variable {f} (p:Spotty f (2*(kSize*l)) (2*(kSize*l)))(w:Signed→A)
include p
lemma worth:Vale (crowd (bowl f) w) l kSize:=by
 intro y v u; choose E H using fun i:y=> (crowd_in _ _ w|>.1 (v i.property) : ∃ s:Signed,f (w s) (s⁻¹.act i.val)); have he:Injective E:=by
    intro i j g; by_contra h; have t:= H i; have pZ:= H j; rw [g] at t
    let z:= E j; have ht:2*(kSize*l)< separation i.val j.val:=by rw [←separation_signed _ _ z⁻¹]; exact (p (w z)).1 _ ((crowd_in ..).2 t) _ ((crowd_in ..).2 pZ) (fun t=> h (Subtype.ext (z⁻¹.act_injective t)))
    exact ht.not_ge (u _ i.property _ j.property)
 simpa [kSize] using Fintype.card_le_of_injective E he
lemma bill(x:Site n): x∈halo (2*(kSize*l)) (crowd (bowl f) w):=by
 apply Corona.halo_mono le_rfl _ ((p (w 1)).2 x); intro i v; exact (crowd_in ..).2 (show bowl f w i from ⟨1,by simpa using (crowd_in ..).1 v⟩)
variable (l f)
def netX : Field n ((Signed→A)×March n) Prop :=fun z i=> bowl f z.1 i ∧ tag l kSize (crowd (bowl f) z.1) z.2 i=0
omit p
lemma sym(h:∀ x:Site n,Moves (Equiv.addLeft x) f): Sym (netX l f):=by
 intro s x; obtain ⟨E,w⟩:= shelter f h s x; let Q:=facet s x; refine ⟨prodCongr E (tumble Q),fun i j=>?_⟩; have he(j):bowl f (E i.1) j↔ bowl f i.1 (Q j):= iff_of_eq (w i.1 j); exact congrArg₂ And (propext (he j)) (congrArg (· = 0) (tag_turn i.2 Q (facet_keeps s x) (S:=crowd (bowl f) (E i.1)) (fun z=> (crowd_in ..).trans ((he z).trans (crowd_in ..).symm)) j)) -- tune implicit
abbrev distD(k l m:ℕ):= k*l+(k*l+m)+k*l
lemma rangeK(p:SplitK n f r): SplitK n (netX l f) (distD kSize l r):=by
 let X:=bowl f; let y:=kSize*l; let Y:=col n y; let F: Field n ((Signed→A) × March n) (Prop × March n):=fun i x=>(X i.1 x,Y i.2 x); have hp: SplitK n F (y+r):= SplitK.product (SplitK.star (bowl_split f p) (by omega)) (SplitK.star (heap n y) (by omega)); apply Uses.epoch _ hp
 intro x u v t; have hu(i)(p:separation x i≤ y):F u i=F v i:=t ((reg_in ..).mpr p); let ht:=hu x (by simp); apply congrArg₂ And (congrArg Prod.fst ht); exact congrArg (· = 0) (tags_p l kSize (S:=crowd X u.1) (fun y V=> (crowd_in ..).trans ((iff_of_eq ((show X u.1 y = X v.1 y from congrArg Prod.fst (hu y V)))).trans (crowd_in ..).symm)) (congrArg Prod.snd ht))
variable {l f}
include p
set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
lemma area : Spotty (netX l f) l (3*(kSize*l)):=by
 rintro ⟨w,i⟩; set S:=crowd (bowl f) w; let B:=worth p w
 let T:=crowd (netX l f) (w,i); have he(x):x∈T↔ x∈S ∧ tag l kSize S i x=0:=by unfold T S; simp only [crowd_in]; rfl
 constructor
 · intro x u y t v; by_contra! e; obtain ⟨w,h⟩:= he _ |>.1 (show x∈T from u); obtain ⟨g,j⟩:= he _|>.1 (show y∈T from t); exact related B w (B.major S l w (arc _ _ g e)) v i (h.trans j.symm)
 intro x; obtain ⟨z,hz,H⟩:= halo_spec.mp (bill p w x); obtain ⟨y,h,g⟩:= has0 B hz i; refine halo_spec.mpr ⟨y,(he _).2 ⟨lit S l hz h,g⟩,?_⟩; have hp:=size S l z y _ h; have ht:= separation_triangle y z x; rw [separation_comm y z] at ht; omega
end Sleet
end YM.CF.BProof.Mesh

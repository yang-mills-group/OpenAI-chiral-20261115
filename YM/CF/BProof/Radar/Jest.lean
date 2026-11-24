import YM.CF.BProof.Radar.Scout
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 4000
set_option maxHeartbeats 720000
noncomputable section
namespace YM.CF.BProof.Mesh
open Lattice Function Finset Equiv Regard Rows
open scoped BigOperators Classical
variable {C A:Type*}{n:Side}{l k r d:ℕ}
namespace Sleet
open Crop.Native Cat Tetra
namespace Play
variable (g:Field n A C)
abbrev pad (w:A)(x:Site n) := patch g w (g w x)
@[simp] lemma pad0 (i:Site n)(w:A): i∈pad g w i:=by simp [pad]
def loud(l r:ℕ) : Field n (A×March n) (C× Fin (r+1)):=fun w i => (g w.1 i, ⟨min r (tag l r (pad g w.1 i) w.2 i),by omega⟩)
variable {g}(p:∀ x c, Vale (patch g x c) l r)
lemma rangeA(t:SplitK n g k) : SplitK n (loud g l r) (r*l+(r*l+k)+r*l):=by
 let F : Field n (A×March n) (C×March n):=fun w i=>(g w.1 i,col n (r*l) w.2 i); have hp:SplitK n F (r*l+k):= SplitK.product (t.star (by omega)) ((heap n (r*l)).star (by omega)); apply Uses.epoch _ hp
 intro x y z H; let d:=r*l; have ht(i)(p:separation x i ≤ d): F y i=F z i:= H ((reg_in ..).mpr p); have hz:F y x= F z x:=ht x (by simp); have hu:g y.1 x=g z.1 x:=congrArg Prod.fst hz
 refine Prod.ext hu (Fin.ext (congrArg (min r) (tags_p l r (S:=pad g y.1 x) (T:=pad g z.1 x) (fun i hi=> ?_) (congrArg Prod.snd hz))))
 simp only [pad,on_patch]; rw [hu,show g y.1 i= _ from (show _= g z.1 i from congrArg Prod.fst (ht i hi))]
lemma turn_e (t:Sym g): Sym (loud g l r):=by
 intro s x; let Q:=facet s x; obtain ⟨E,H⟩:= t s x; refine ⟨prodCongr E (tumble Q),fun i j=>?_⟩; exact Prod.ext (H i.1 j) (Fin.ext (congrArg (min r) (tag_turn (S:=pad g (E i.1) j) (T:=pad g i.1 (facet s x j)) _ Q (facet_keeps s x) (fun y => by simp only [pad,on_patch,H,Q]) j)))
include p
lemma orderX : OrderC (loud g l r) l:=by
 intro x y u l' t k; let f:=g t.1; have he:f x=f y:=congrArg Prod.fst k; let c:= f x; let P:=patch g t.1 c; have hx:x∈P:=pad0 ..; have hy:y∈ P:=(on_patch ..).mpr he.symm; have hk: min r (tag l r P t.2 x)= min r (tag l r (pad g t.1 y) t.2 y) := congrArg (Fin.val ∘ Prod.snd) k; rw [show pad g t.1 y=P from congrArg (patch g t.1) he.symm,min_eq_right (tag_age (p t.1 c) _ hx).le,min_eq_right (tag_age (p t.1 c) _ hy).le] at hk; exact related (p t.1 c) hx ((p t.1 c).major P l hx (arc _ _ hy l')) u _ hk
end Play
abbrev stage0(l:ℕ):=2*(kSize*l)
abbrev Circus(l:ℕ) := grSize (cover (stage0 l)) -- remove
abbrev Darts(l:ℕ):= Finset ↑(shell (cover (stage0 l))) × Fin (kSize+1)
abbrev Syr(l:ℕ):= Fintype.card (Darts l)
abbrev Veep(l:ℕ)(n:Side):= Earsa (stage0 l) n × March n
def many(l:ℕ)(n:Side):Field n (Veep l n) (Darts l):= Play.loud (orbit (Hop (stage0 l) n) (cover (stage0 l))) l kSize
abbrev majesty(l:ℕ):=let L:=stage0 l; let K:=cover L; let Z:= kSize*l; Z+(Z+(K+pay_l L+K))+Z
variable (l n)
lemma pity (t:2*(2*(kSize*stage0 l))<n.val):Nonempty (Veep l n)∧OrderC (many l n) l∧ Sym (many l n)∧ SplitK n (many l n) (majesty l):=by
 have hp:=haveH n (stage0 l) t; obtain ⟨hx,hu,x,v⟩:=hp; have HV:= nonE n; exact ⟨inferInstance,Play.orderX (fun i a=> crown _ v i a),Play.turn_e (Loyal.keep (senses _ _) x),Play.rangeA (Uses.epoch (uses _ _) hu)⟩
end Sleet
end YM.CF.BProof.Mesh

import YM.SU5.Intrinsic.Coil.Firing

/-! Keep the witness $K$ at the flagged visits. Uses *same purchased cost map* over all such uses. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 22000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Coil.Chart
open Function Lattice Finset Filter Stilo Palot RG Scree Skye Fock Tulip Sour
open Cube Pastry Vow Rue Stax Sault
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {I:Type}[DecidableEq I][Fintype I]{n:Side} (F:ForceBudget n) (P:BudgetPoint) (H:ℝ) (δ:ℕ)
structure Blizzard (b: Force n→ℝ):Prop where
 costs (i): Fray P H δ (lordD i) (extraD i) (F i) (b i)
 rate:0≤b
-- fire.
variable {F P H δ} {b:Force n→ℝ}{V:I→ Firing n}{a:I→ℝ}{B:Chart I (Seat n)}
namespace Stoke
variable (C:B.Stoke δ P H V a)
end Stoke
variable (T:Blizzard F P H δ b)
def Pun (B:Chart I (Seat n))(L:Finset (I ⊕ Force n))(X: Aura n)(D: Support (More n)):Prop:= B.ledger.melody L=beamH X.val ∧ B.ledger.Pairwise L ∧ B.ledger.claim L=D
lemma splitK(L:Finset (I ⊕ Force n)): L.toLeft.disjSum L.toRight=L:=by ext i; cases i<;>simp
lemma old_flag (B:Chart I (Seat n))(L:Finset (I ⊕ Force n)) : L.toRight.biUnion extraD=B.ledger.claim L :=by rw [←B.claim_tape L.toLeft L.toRight, splitK]
namespace Pun
variable {X: Aura n}{D: Support (More n)}{L: Finset (I⊕ Force n)}(u: Pun B L X D)
include u
lemma tuneSpace : B.ledger.foot L=X.val:= by rw [←Album.tune,u.1,bay_beam]
lemma used (i)(h:i∈L): (B.ledger.seats i) ⊆ X.val:= (u.tuneSpace) ▸ (B.ledger.atLine L h)
lemma markers : D⊆ X.val:=by rw [←u.2.2,← u.tuneSpace]; exact B.ledger.claims L
lemma meets : B.ledger.Pays D L:=⟨u.2.1,by rw [u.tuneSpace, inter_eq_right.mpr u.markers,u.2.2]⟩
lemma lower (i:Force n)(h:i∈L.toRight) : (lordD i).val ⊆ X.val ∧ (lordD i).val ∩ D=i.val.2 := by -- placeholder
 have he:Sum.inr i∈ L:=mem_toRight.mp h; exact ⟨u.used _ he, B.sure_Flag u.meets i he⟩
include T
lemma oldHas (x: Orbit n)(t:(∏ i∈ L.toRight, F i x)≠ 0): halo δ D ⊆ X.val ∧ D ⊆flags P.threshold x.1:=by
 have v(i:Force n)(h:i∈L.toRight):= (T.costs i).loaf x (fun g=> t (prod_eq_zero h g))
 have he: L.toRight.biUnion extraD=D:= (old_flag B L).trans u.2.2
 constructor
 · intro i t; obtain ⟨j,q,l⟩:=halo_spec.mp t; rw [←he] at q; obtain ⟨t,h,u'⟩:=mem_biUnion.mp q; exact (u.lower t h).1 ((v _ h).1 (halo_spec.mpr ⟨_,u',l⟩))
 intro i h; obtain ⟨j,g,v'⟩:=mem_biUnion.mp (show i∈ L.toRight.biUnion extraD from he.symm ▸ h); exact (v j g).2 v'
lemma oldFuel (t:0 ≤ H) : Fray P H δ X D (∏ i∈ L.toRight,F i) (∏ i∈L.toRight,b i):=by
 refine ⟨Medal.prodP _ _ _ ?_ t, fun i p=> u.oldHas T i (by simpa only [Finset.prod_apply] using p)⟩ -- signature T before u vs after?
 intro i hi; let a:= (u.lower i hi).1; have hp: extraD i=(lordD i).val∩D:=(u.lower i hi).2.symm; refine (T.costs i).merit.stretchB a (hp.symm ▸ inter_subset_right) ?_
 intro j v; obtain ⟨h,v⟩:=mem_sdiff.mp v; exact mem_sdiff.mpr ⟨a h,fun g=> v (hp.symm ▸ mem_inter.mpr ⟨h,g⟩)⟩
omit T
lemma no_old (q:D=∅): L.toRight=∅:=by
 by_contra h; obtain ⟨i,g⟩:=nonempty_iff_ne_empty.mpr h; obtain ⟨k,b⟩:=i.property.1; exact notMem_empty k ((((old_flag B L).trans u.2.2).trans q) ▸ (show k∈ L.toRight.biUnion extraD from mem_biUnion.mpr ⟨_,g,b⟩)) -- eq funny
end Pun

namespace Stoke
variable (C:B.Stoke δ P H V a)
variable {S:Aura n}{D: Support (More n)}{L:Finset (I ⊕ Force n)}
variable (u:Pun B L S D)(α:halo δ D ⊆ S.val)
include u α C
lemma active (i)(h:i∈ L.toLeft): B.space i⊆ S.val:= u.used _ (mem_toLeft.mp h)
def roll (G: Copy n)(l:List I):Copy n:= l.foldr (fun i x=> if h:i∈ L.toLeft then C.housing S D u.markers α i (active C u α i h) x else x) G
lemma roll_cons (G:Copy n)(i:I)(l:List I): C.roll u α G (i::l)= if h:i∈ L.toLeft then C.housing S D u.markers α i (active C u α i h) (C.roll u α G l) else C.roll u α G l := rfl
lemma roll_eq (G: Copy n)(l:List I)(x:Orbit n)(p:x.1∈σX P S D): C.roll u α G l x=sail (C.gives x) L.toLeft l (G x):=by
 induction l with
 | nil=> rfl
 | cons i l ih=>
    rw [C.roll_cons,sail,List.foldr_cons]; by_cases v:i∈ L.toLeft; · rw [dif_pos v,if_pos v, C.houses _ _ _ _ _ _ _ _ p, ih]; rfl
    rw [dif_neg v,if_neg v]; exact ih
lemma rollFray (G: Copy n)(c:ℝ)(p:Fray P H δ S D G c)(l:List I)(hp:l.Nodup)(h0:3 ≤ P.B)(t:0≤H): Fray P H δ S D (C.roll u α G l) ((∏ i∈ (L.toLeft ∩ l.toFinset), a i)*c):=by
 induction l with
 | nil=> simpa only [roll,List.foldr_nil,List.toFinset_nil,inter_empty,prod_empty,one_mul] using p
 | cons i l ih=>
    rw [C.roll_cons,List.toFinset_cons]; obtain ⟨hi,b⟩:= List.nodup_cons.mp hp; by_cases v:i∈L.toLeft; swap; · rw [dif_neg v,inter_insert_of_notMem v]; exact ih b
    rw [dif_pos v,inter_insert_of_mem v,prod_insert (fun p=>hi (List.mem_toFinset.mp (mem_inter.mp p).2)),mul_assoc]; exact C.housing_toll S D u.markers α t h0 _ _ _ _ (ih b)
lemma rollHat (G:Copy n)(x:Orbit n)(τ:Ids n)(p:D=∅)(q:G x=G (x.1,τ))(l:List I): C.roll u α G l x=C.roll u α G l (x.1,τ):=by
 induction l with
 | nil=> exact q
 | cons i l ih=>
    rw [C.roll_cons]; split; exact C.houseVoid S D u.markers α _ _ _ x τ ih p; exact ih
end Stoke
end YM.CF.Coil.Chart

import YM.CF.BProof.Radar.Star
/- consult order array on sets of sites; gives iid perms to mint component choices -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.BProof.Mesh
open Lattice Function Finset Equiv Regard
open scoped BigOperators Classical
variable {A B U V:Type*}{n: Side}{p d o r:ℕ}{l:ℕ}

namespace Rows
abbrev Code (S:Support n):= S ≃ Fin S.card
abbrev March(n:Side):= ∀ S:Support n,Code S
private def present(S:Support n): Code S:=(Fintype.equivFin S).trans (finCongr (by simp))
lemma nonE (n:Side) : Nonempty (March n):=⟨fun S=> present S⟩
def order (l:ℕ)(i:Site n)(P:March n): March n:=fun S=>if i∈S∧ S⊆region n i l then P S else present S
abbrev col(n:Side)(l:ℕ):Field n (March n) (March n):= fun x i=>order l i x
lemma heap(n:Side)(l:ℕ): SplitK n (col n l) l:=by
 intro a b t; let R(S:Support n):Prop:=∃ x∈ b,x ∈ S∧ S⊆region n x l; let e(S:Support n):= if R S then (prodComm (Code S) _) else Equiv.refl _; let E:= piece _ e
 have hp{s:Site n}{S:Support n}(p:s∈ S∧S⊆region n s l)(u:s ∈ a): ¬ R S:= by rintro ⟨x,hx,v,t'⟩; exact (t s u x hx).not_ge (reg_in ..|>.mp (p.2 v))
 refine ⟨E,penMake _ _ _ _ fun z=>?_⟩; let X:= E z
 have h(S:Support n): e S (z.1 S,z.2 S)=(X.1 S,X.2 S):=rfl
 have h1(s: Site n)(p:s∈ a): (col n l X.1 s,col n l X.2 s)=(col n l z.1 s,col n l z.2 s):=by
    refine Prod.ext (funext fun i=>?_) (funext fun i=>?_)
    all_goals unfold col order; dsimp only; by_cases w:s∈i ∧ i ⊆region n s l -- tune
    any_goals rw [if_neg w,if_neg w]
    · rw [if_pos w,if_pos w]; exact congrArg Prod.fst ((h i).symm.trans (hp w p|> fun u=>by unfold e; rw [if_neg u]))
    rw [if_pos w,if_pos w]; exact congrArg Prod.snd ((h i).symm.trans (hp w p|> fun u=>by unfold e; rw [if_neg u]))
 have h2(s: Site n)(p:s∈ b): (col n l X.1 s,col n l X.2 s)=(col n l z.2 s,col n l z.1 s):=by
    refine Prod.ext (funext fun i=>?_) (funext fun i=>?_); all_goals unfold col order; dsimp only; by_cases w:s∈i∧ i⊆region n s l
    any_goals rw [if_neg w,if_neg w]
    · rw [if_pos w,if_pos w]; exact congrArg Prod.fst ((h i).symm.trans (by rw [show e i=prodComm _ _ from if_pos (show R i from ⟨s,p,w⟩)]))
    rw [if_pos w,if_pos w]; exact congrArg Prod.snd ((h i).symm.trans (by rw [show e i=prodComm _ _ from if_pos (show R i from ⟨s,p,w⟩)]))
 exact ⟨fun i p=>congrArg Prod.fst (h1 i p),fun i p=>congrArg Prod.snd (h1 i p),fun i p=>congrArg Prod.fst (h2 i p),fun i p=>congrArg Prod.snd (h2 i p)⟩
-- symmetry.Of pre arrays
variable (e:Perm (Site n))
def writeE : Perm (Support n) where
 toFun S:= S.map e.toEmbedding
 invFun S:= S.map e.symm.toEmbedding
 left_inv S:= by ext; simp
 right_inv S:=by ext; simp
lemma write_mem(i:Support n)(x:Site n):e x ∈ writeE e i ↔ x∈i:=by change _∈ i.map _ ↔ _; simp
private def country (S:Support n): S≃ (writeE e S):= (Equiv.subtypeEquiv e (fun i=> (write_mem e S i).symm))
private def rotateE (S: Support n) : Code (writeE e S)≃ Code S:= Equiv.equivCongr (country e S).symm (finCongr (card_map _))
def tumble:Perm (March n):= (Equiv.piCongrLeft (fun i:Support n=> Code i) (writeE e)).symm.trans (Equiv.piCongrRight (rotateE e))
-- key equality when using permutation. formulate Nat projection
lemma tumbles (x:March n)(S:Support n)(T: Support n)(w:writeE e S=T)(i:Site n)(p:i∈S)(v:e i∈ T) : (tumble e x S ⟨i,p⟩).val=(x T ⟨e i,v⟩).val:=by subst T; rfl
end Rows
end YM.CF.BProof.Mesh

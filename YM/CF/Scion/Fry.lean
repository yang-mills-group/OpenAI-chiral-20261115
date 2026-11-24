import YM.CF.Palot.Pal
import YM.CF.Urn.Role
import YM.CF.Reine.King
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Scion
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake
variable {ι A n M: Type*}[LinearOrder n][Fintype n][LinearOrder M][Fintype M]
-- local even word cert
abbrev Fit (T:Set ι)(P:List ι):Prop:= ∀ i∈P,i∈T
inductive Pitch (F:ι→ FC n)(S:Set ι)(b:ℕ): FC n→Prop where
 | term (P:List ι): Nat.ModEq 2 P.length b → Fit S P→Pitch F S b (rollC F P)
 | null : Pitch F S b 0
 | add {x y}: Pitch F S b x → Pitch F S b y → Pitch F S b (x+y)
 | stam {x} (c:ℂ): Pitch F S b x→Pitch F S b (c • x)
variable {F:ι→FC n}{b c:ℕ}{S T:Set ι}{x y:FC n}
lemma Pitch.sum {G:A→ FC n}(X:Finset A)(h:∀ i∈X,Pitch F S b (G i)): Pitch F S b (∑ i∈X,G i):=by
 classical
 induction X using Finset.induction_on with | empty=>rw [sum_empty]; exact Pitch.null| insert i X p ih=> rw [sum_insert p]; exact Pitch.add (h i (mem_insert_self ..)) (ih fun i t=>h i (mem_insert_of_mem t))
lemma Pitch.listS {L:List A}{G:A→FC n}(h:∀ i∈L,Pitch F S b (G i)): Pitch F S b (L.map G).sum:=by induction L with| nil=> exact Pitch.null| cons i L ih=> exact Pitch.add (h i (List.mem_cons_self ..)) (ih fun j p=> h j (List.mem_cons_of_mem i p))
lemma Pitch.grade (p:Pitch F S b x)(q:Nat.ModEq 2 b c):Pitch F S c x:=by induction p with|null=>exact Pitch.null| stam w _ h=>exact Pitch.stam w h| add _ _ h g=>exact Pitch.add h g| term i u v=>exact Pitch.term i (u.trans q) v
lemma Pitch.rise (p:Pitch F S b x)(q:S ⊆T):Pitch F T b x:=by induction p with| null=> exact Pitch.null| stam w _ h=> exact Pitch.stam w h| add _ _ h g=> exact Pitch.add h g| term i u v=> exact Pitch.term i u fun j w=> q (v j w)
lemma Pitch.mu (p:Pitch F S b x)(q:Pitch F S c y):Pitch F S (b+c) (x*y):=by
 classical
 induction p with
 | term i u v=>
    induction q with
    | term j t h=> rw [←Hake.lump]; apply Pitch.term _; rw [List.length_append]; exact u.add t; exact fun l h'=> (List.mem_append.mp h').elim (v l) (h l)
    | null=> rw [mul_zero]; exact Pitch.null
    | add r s e a=> rw [mul_add]; exact Pitch.add e a
    | stam w p h=> rw [Algebra.mul_smul_comm]; exact Pitch.stam w h
 | null=> rw [zero_mul]; exact Pitch.null
 | add _ _ r s=> rw [add_mul]; exact Pitch.add r s
 | stam w _ r=> rw [Algebra.smul_mul_assoc]; exact Pitch.stam w r
lemma zeroW(S:Set ι):Pitch F S 0 1:= Pitch.term [] rfl (by simp [Fit])
lemma oneW {i:ι}(p:i∈ S):Pitch F S 1 (F i):=by rw [show F i=rollC F [i] by simp [rollC]]; exact Pitch.term [i] rfl (by simp [Fit,p])
lemma fresh_p {Z:Finset n}(h:Flour Z x):Pitch (put (n:=n)) (Z:Set n) 0 x:=by
 rw [h.pin]; apply Pitch.sum; intro j p; apply Pitch.stam
 change Pitch (put (n:=n)) _ 0 (rollC put (j.sort (·≤·))); obtain ⟨u,v⟩:=mem_filter.mp p
 apply Pitch.term _; rw [length_sort]; obtain ⟨w,g⟩:=v; unfold Nat.ModEq; omega
 exact fun i l=> mem_powerset.mp u ((Finset.mem_sort ..).mp l)
private lemma pairR {Z:Finset n}(j:List n)(h:Even j.length)(p:Fit (Z:Set n) j): Flour Z (rollC put j):=by
 induction hk:j.length using Nat.strong_induction_on generalizing j with
 | h a ih=> cases j with
            | nil=> exact Flour.grainE
            | cons i j=> cases j with
                        | nil=> simp at h
                        | cons y l=>
                            have hs:Even l.length:=by obtain ⟨x,h⟩:=h; simp only [List.length_cons] at h; exact ⟨x-1,by omega⟩
                            have ht:Fit (Z:Set n) l:=fun z u=> p z (by simp [u]); rw [show rollC put (i::y::l)=put i*put y*rollC put l by rw [mul_assoc]; rfl]; apply (Flour.putPut Z (p i (by simp)) (p y (by simp))).mul; apply ih _ _ _ hs ht rfl; simp only [List.length_cons] at hk; omega
lemma fry_p {Z:Finset n}(g:Pitch (put (n:=n)) (Z:Set n) b x)(h: Even b): Flour Z x:=by
 induction g with
 | term i p u=> refine pairR i ?_ u; obtain ⟨v,h⟩:=h; unfold Nat.ModEq at p; exact ⟨i.length/2, by omega⟩
 | null=> exact Flour.trivial
 | add _ _ s t=> exact s.add t
 | stam c _ t=> exact t.smul c
end YM.CF.Scion

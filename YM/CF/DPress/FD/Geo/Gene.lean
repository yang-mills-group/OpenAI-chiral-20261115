import YM.CF.DPress.FD.Geo.Scale
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Finset Cash Bifold Deck Hue
open scoped Topology BigOperators ENNReal NNReal Classical
variable {n:Side} {q l:ℕ} {i j:Site n}
namespace Geo
abbrev ColorT(q:ℕ)(n:Side):= Site n→ Fin q
abbrev Tight (c:ColorT q n)(l:ℕ): Prop:= ∀ (i j:Site n),i≠j→ close l i j→ c i ≠ c j
def propL(c:ColorT q n)(l:ℕ) (S:Support n)(k:ℕ)(i:Site n):Prop:= (c i).val=k∧∀ j∈ S,l<separation i j
def pics(c:ColorT q n)(l:ℕ): ℕ→ Support n
| 0=>∅
| k+1=> let a:=pics c l k; a ∪ univ.filter (propL c l a k)
local notation "X" => pics
variable (c e:ColorT q n)
lemma tic {k:ℕ} : i ∈ X c l (k+1)↔ i∈ X c l k∨ propL c l (X c l k) k i:=by rw [pics]; simp
lemma swell : Monotone (X c l):= monotone_nat_of_le_succ (fun x i p=> (tic c).mpr (Or.inl p))
lemma growP (t:Tight c l)(k:ℕ):Lonely (X c l k) l:=by
 induction k with
 | zero=> intro i v; simp [pics] at v
 | succ k H=>
  intro i v j b x; rw [tic] at v b; rcases v with v|v <;> rcases b with b|b
  · exact H i v j b x
  · exact (b.2 _ v).trans_eq (separation_comm ..)
  · exact v.2 _ b
  by_contra! hp; have hh:close l i j:= hp.trans (show l ≤ s10 l from (by unfold s10; omega)); exact t i j x hh (Fin.ext (v.1.trans b.1.symm))
-- coverage.Cir. Need existence via stage k. no symmetry assumption.
lemma full (i: Site n)(l:ℕ):∃ j∈X c l q,separation i j≤ l:=by
 let k:=(c i).val; let D:= X c l k; have he:k<q:=(c i).isLt
 by_cases h:∃ j∈D,separation i j≤ l; · obtain ⟨j,t,p⟩:=h; exact ⟨j,(swell c he.le) t,p⟩
 have hp:i∈X c l (k+1):= (tic c).2 (Or.inr ⟨rfl,fun j v=>lt_of_not_ge fun t=>h ⟨j,v,t⟩⟩); exact ⟨i,(swell c he) hp,(separation_self i).trans_le (Nat.zero_le _)⟩
lemma scene(u v:ℕ)(p:u≤v):cell n i u⊆cell n i v:= fun j t=> (cellP ..).2 (((cellP ..).1 t).trans p)
lemma closer{r s:ℕ}(p:separation i j≤r): cell n j s⊆ cell n i (s+r):=fun k q=>(cellP ..).2 ((separation_triangle i j k).trans ((add_le_add p ((cellP ..).1 q)).trans_eq (add_comm ..)))
lemma ticket (k:ℕ)(i: Site n)(t:Set.EqOn c e (cell n i (k*l))) : i∈ X c l k ↔ i∈ X e l k:=by
 induction k generalizing i with
 | zero=> simp [pics]
 | succ k h =>
   rw [tic,tic,h i (t.mono (show _≤ (↑(cell n i ((k+1)*l)):Set _) from Finset.coe_subset.mpr (scene _ _ (by rw [add_mul,one_mul]; omega))))]; apply or_congr_right; unfold propL; rw [t (show i∈cell n i ((k+1)*l) from (cellP ..|>.2 (by simp)))]; refine and_congr_right fun r=> ?_
   have hp(j:Site n)(v:separation i j ≤ l):j∈ pics c l k ↔ j∈ pics e l k:= h j (t.mono (Finset.coe_subset.mpr (by simpa only [add_mul,one_mul] using (closer (s:=k*l) v)))) -- coercion syntax
   constructor <;> intro u j t <;> by_contra! y; · exact (u j ((hp j y).2 t)).not_ge y
   exact (u j ((hp j y).1 t)).not_ge y
lemma sweep (p: Equiv.Perm (Site n))(t:c=e ∘ p)(v:∀ i j:Site n,separation (p i) (p j)= separation i j)(k l:ℕ)(i:Site n):i∈pics c l k↔ p i∈pics e l k:=by
 induction k generalizing i with
 | zero=> simp [pics]
 | succ k h=>
   rw [tic,tic,h]; apply or_congr_right; unfold propL; rw [show c i=e (p i) from congrFun t i]; refine and_congr_right fun x=> ?_; constructor
   · intro t' l p'; obtain ⟨l,rfl⟩:= p.surjective l; exact (t' l ((h _).2 p')).trans_eq (v _ _).symm
   intro t' l p'; exact (t' (p l) ((h _).1 p')).trans_eq (v _ _)
end Geo
end YM.CF.DPress.FD

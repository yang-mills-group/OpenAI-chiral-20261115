import Gingham.Ruff.Quetzal
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Finset Function Fock Branch Drapes Filter
attribute [local instance] opCStarAlgebra

variable {I Y D G : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y] [TopologicalSpace D]
variable {b : Stage Y I D G} {s t u : Tag b} {A B C : Raw D I} {L : License D}

variable {S : Seal Y}{c d : Toll I} {a r m q : ℝ} {R:Seal Y→Prop}

lemma strip_i (w:Y)(A:Op I)(i j): (strip b {w} * A) i j=if b.home i=w then A i j else 0:=
 by rw [stripL]; simp only [mem_singleton]
lemma strip_j (w:Y)(A:Op I)(i j): (A*strip b {w}) i j=if b.home j=w then A i j else 0:=
 by rw [stripR]; simp only [mem_singleton]


lemma streami (w:Y)(p:Suite L s t S c A): Suite L s t S
     (fun i j=>if b.home i=w then c i j else 0) (fun x=>strip b {w} * A x):=by
 refine ⟨⟨?_,?_⟩,?_⟩
 · intro i x
   rw [mul_assoc,p.frame i x,←mul_assoc,strip_tag s,mul_assoc]
 · intro i j
   by_cases g:b.home i=w
   · simpa only [strip_i,if_pos g] using p.expo i j
     -- RHS? goal simplification via simpa
   simp only [strip_i,if_neg g]
   exact nothing ..
 · intro i j
   simp only [strip_i]
   split
   · exact p.fuel i j
   exact L.con _

lemma Brooch.streami (w:Y)(p:Brooch R L s t a r A):
 Brooch (fun X=>w∈X ∧ R X) L s t a r (fun x=>strip b {w} * A x) :=by
 obtain ⟨N,C,g,v,k,m'⟩:=p
 refine ⟨_,_,fun S=> Ruff.streami w (g S),v.lowers ?_,?_,?_⟩
 · intro S i j
   apply mul_le_mul_of_nonneg_left _ (rent_pos ..).le
   split
   · exact le_rfl
   exact (g S).nonn i j
 · intro x; dsimp only; rw [k,mul_sum]
 · intro S i j u
   change (if b.home i=w then C S i j else 0)≠0 at u
   split at u
   · rename_i k
     exact ⟨k ▸ ((g S).expo i j).triggered u|>.2.1,m' _ _ _ u⟩
   exact False.elim (u rfl)


lemma streamj (w:Y)(p:Suite L s t S c A): Suite L s t S
     (fun i j=>if b.home j=w then c i j else 0) (fun x=>A x * strip b {w}):=by
 refine ⟨⟨?_,?_⟩,?_⟩
 · intro i x
   rw [mul_assoc,strip_tag t,←mul_assoc,p.frame i x,mul_assoc]
 · intro i j
   by_cases g:b.home j=w
   · simpa only [strip_j,if_pos g] using p.expo i j
     -- RHS? goal simplification via simpa
   simp only [strip_j,if_neg g]
   exact nothing ..
 · intro i j
   simp only [strip_j]
   split
   · exact p.fuel i j
   exact L.con _

lemma Brooch.streamj (w:Y)(p:Brooch R L s t a r A):
 Brooch (fun X=>w∈X ∧ R X) L s t a r (fun x=>A x * strip b {w}) :=by
 obtain ⟨N,C,g,v,k,m'⟩:=p
 refine ⟨_,_,fun S=> Ruff.streamj w (g S),v.lowers ?_,?_,?_⟩
 · intro S i j
   apply mul_le_mul_of_nonneg_left _ (rent_pos ..).le
   split
   · exact le_rfl
   exact (g S).nonn i j
 · intro x; dsimp only; rw [k,sum_mul]
 · intro S i j u
   change (if b.home j=w then C S i j else 0)≠0 at u
   split at u
   · rename_i k
     exact ⟨k ▸ ((g S).expo i j).triggered u|>.2.2,m' _ _ _ u⟩
   exact False.elim (u rfl)


lemma Brooch.take (n:ℝ) (hn:0≤n)(h: ∀ S i j,Grove b.F S→b.home i∈S→b.home j∈S →
                                  R S → rent m S ≤ n*rent a S)(p:Brooch R L s t a r A):
     Brooch R L s t m (n*r) A :=by
 obtain ⟨N,C,g,v,k,u⟩:=p
 refine ⟨N,C,g,(v.funds hn).lowers ?_,k,u⟩
 intro S i j
 rw [←mul_assoc,mul_comm _ n]
 by_cases t:C S i j=0
 · simp [t]
 obtain ⟨p,t₁,t₂⟩:=((g S).expo i j).triggered t
 exact mul_le_mul_of_nonneg_right (h S i j p t₁ t₂ (u S i j t)) ((g S).nonn i j)


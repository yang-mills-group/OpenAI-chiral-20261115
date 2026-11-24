import Merino.Cuff.Ink
set_option autoImplicit false
noncomputable section
namespace YM.CF.Merino.Cuff
open Function Finset Lattice Wilson
open scoped InnerProductSpace Topology
variable {G:Gauge}{N:Side}


abbrev BoltIx(G:Gauge)(N:Side):=Edge (Site N)× Chips G
abbrev eseed (X:RG.Directions G N)(i:BoltIx G N):=dust i.2 (X i.1)
open Font
/-- conservative distance tariff. -/
def lead(k:ℕ):=9*(k+1)+1
def leadPrice (k:ℕ):ℝ:=4*(lead k:ℝ)^2
abbrev odds (o:Site N)(i:BoltIx G N):=leadPrice (separation o i.1.1)
lemma odds_pos(o:Site N)(i:BoltIx G N):0≤odds o i:=mul_nonneg (by norm_num) (sq_nonneg _)

structure Grooved (o:Site N)(k:ℕ)(L:BoltIx G N→Husk G N→ℝ):Prop where
  light(i):∑ j,|L i j| ≤ odds o i
  nearby(i j): L i j≠0 → separation o j.1.1 ≤ lead k
  tick(u:RG.Directions G N)(i:BoltIx G N)(v:separation o i.1.1≤k):
     eseed (u-Font.pure (sap o u)) i= ∑ j,L i j * cseed u j


lemma pickGroove (G:Gauge)(o:Site N){k:ℕ}(hf:lead k<N.val):∃ L:BoltIx G N→Husk G N→ℝ,Grooved o k L:=by
 classical
 choose A ha hx hu using funnel G.Color o
 let P (i:BoltIx G N)(j:Husk G N):=if separation o i.1.1≤k then if j.2=i.2 then A i.1 (.inl j.1) else 0 else 0
 have e(i:BoltIx G N)(v:separation o i.1.1≤k):Font.slope o i.1+1≤ lead k:=by unfold Font.slope lead; omega
 have g(i:BoltIx G N)(v:separation o i.1.1≤k)(a:Axis):A i.1 (.inr a)=0:=by
    by_contra h
    exact Nat.not_lt.mpr ((hx _ _ h).trans (e i v)) hf
 refine ⟨P,?_,?_,?_⟩
 · intro i; by_cases v:separation o i.1.1≤k
   · have t:=ha i.1
     rw [Fintype.sum_sum_type] at t
     simp only [g i v,abs_zero,sum_const_zero,add_zero] at t
     unfold Husk P; rw [Fintype.sum_prod_type]
     simpa [v,odds,leadPrice,lead,Font.slope,apply_ite abs] using t
   simp only [P,if_neg v,abs_zero,sum_const_zero]; exact odds_pos ..
 · intro i j p; unfold P at p
   split_ifs at p with u
   · exact (hx i.1 (.inl j.1) p).trans (e i u)
   all_goals contradiction


 intro u i v
 have t:=hu i.1 u
 rw [Fintype.sum_sum_type] at t
 simp only [g i v,zero_smul,sum_const_zero,add_zero] at t
 unfold Husk eseed
 rw [t,Fintype.sum_prod_type (fun (j:Husk G N)=>P i j*cseed u j)]
 change EuclideanSpace.proj i.2 _ = _
 rw [map_sum]
 apply sum_congr rfl; intro a _
 rw [map_smul,sum_eq_single_of_mem i.2 (mem_univ _)]
 · simp only [P,v,if_true]; cases a; rfl
 intro b _ hb; simp only [P,v,if_true,hb,if_false,zero_mul]
end YM.CF.Merino.Cuff

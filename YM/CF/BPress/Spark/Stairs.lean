import YM.CF.BPress.Spark.Timber
/-! rooted Cash for actual configurations. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Spark
open Function NormedSpace Finset Filter Lattice Branch Push.AbsoluteSums Grid RG Ledger MeasureTheory SU Pastry Tulip Skye Girt Scree Cube Lat Fock Vesper Spin Spin.Paint Pine Lily Pledge -- tune
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ContDiff Real ENNReal Classical YM.CF.BPress.Vesper
attribute [local instance] opCStarAlgebra
variable {N:Side}{I J :Type}[Fintype I][Fintype J][DecidableEq I][DecidableEq J]{b:ℕ}{w e a q t:ℝ}
lemma stairs {X:I→Support (More N)} {v:I→ℝ}{J:I→Type}[∀ i,Fintype (J i)](c:Sigma J→ℝ)(p:Cash X v a e)(h:∀i,0≤c i)(l:∀i,∑ j:J i,c ⟨i,j⟩≤ v i): Cash (fun i:Sigma J=> X i.1) c a e:= by
 refine ⟨h,fun i=>?_⟩; refine ⟨fun x=>?_,(hasSum_fintype _).summable,?_ ⟩; unfold Ledger.score; split; exact mul_nonneg (Real.exp_pos _).le (h _); exact le_rfl
 apply le_trans ?_ (budget_sum (p.hits i) univ); rw [tsum_fintype,Fintype.sum_sigma]; apply sum_le_sum; intro j _; unfold Ledger.score; by_cases g:i∈ X j; simp only [g,ite_true]; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (l j) (Real.exp_pos _).le; simp only [g,ite_false,sum_const_zero,le_refl] -- tune
lemma floors {X :I→ Support (More N)}{Y :J→Support (More N)}{v:I→ℝ}{s:J→ℝ}(u:Cash X v a e)(h:Cash Y s a q): Cash (Sum.elim X Y) (Sum.elim v s) a (e+q):=by
 let X':= Sum.elim X Y; let v':= Sum.elim v s; have ht(i):0≤v' i:=by cases i; exact u.pos _; exact h.pos _
 refine ⟨ht,fun i=>?_⟩; refine ⟨fun x=>?_, (hasSum_fintype _).summable,?_⟩; unfold Ledger.score; split; exact mul_nonneg (Real.exp_pos _).le (ht _); exact le_rfl
 have hf(x:I): Ledger.score X' v' a i (.inl x)=Ledger.score X v a i x:=rfl; have hp(x:J) : Ledger.score X' v' a i (.inr x)=Ledger.score Y s a i x:=rfl
 rw [tsum_fintype,Fintype.sum_sum_type]; change (∑ x:I, Ledger.score X' v' _ _ (.inl x))+(∑ y:J, Ledger.score X' v' _ _ (.inr y))≤_; simp_rw [hf,hp]; exact add_le_add (budget_sum (u.hits i) univ) (budget_sum (h.hits i) univ)
namespace Payer
variable {K:I→ Site (More N)} {X:I→ Support (More N)} {C:Token I N}{B:ℕ}(v:Payer K X C a e B)
include v
lemma decks : Cash (fun i=>dorm B (X i)) (raw_bill C a) (δPort B) (aPort B e):= dealer.bark _ _ _ v.care (fun i=>sum_nonneg (fun j _=> mul_nonneg (v.bill i j) (pow_nonneg (zero_le_one.trans v.hold) _))) B e v.cruise v.stake
lemma bill_st (P:I→ Finset (Finset (Dwell N))) : Cash (fun i:Sigma (fun i=> ↥(P i))=> dorm B (X i.1)) (fun i=> C i.1 i.2.val*a^i.2.val.card) (δPort B) (aPort B e):=by
 let F(x:I)(j:Finset (Dwell N)):= C x j*a^j.card; have ht(i j):0≤ F i j:=mul_nonneg (v.bill ..) (pow_nonneg (zero_le_one.trans v.hold) _); apply stairs (N:=N) (J:=fun i=> ↥(P i)) _ (v.decks) (fun i=> ht i.1 i.2.val); intro i; exact (sum_attach (P i) (F i)).le.trans (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _=>ht i j)) -- tune
lemma bill_empty: Cash (fun i=>dorm B (X i)) (fun i=> C i ∅) (δPort B) (aPort B e):=by
 apply v.decks.subs (fun i=> v.bill ..); intro i; have ht:= single_le_sum (s:=(univ:Finset (Finset (Dwell N)))) (f:=fun j=> C i j*a^j.card) (fun j _=> mul_nonneg (v.bill ..) (pow_nonneg (zero_le_one.trans v.hold) _)) (mem_univ ∅); exact (by simpa only [card_empty,pow_zero,mul_one] using ht) -- tune
end Payer
end YM.CF.BPress.Spark

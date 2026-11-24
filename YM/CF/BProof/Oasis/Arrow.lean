import YM.CF.BProof.Oasis.Shale
/-! Generic Dew expansion of mutually exclusive choices; and of exponential
of nonconstant monomials. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Crystal.Dew
open Function Filter Fock Finset NormedSpace Garden Align Wick Double Pastry MeasureTheory Sprinkle
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {V I: Type}[DecidableEq V][Fintype V][Fintype I][LinearOrder I]
variable {f:V→Type}[∀ i,Fintype (f i)] [∀ i, DecidableEq (f i)]
abbrev orts (A:Dew V I)(F:V→ℂ)(i:V): Dough I:=hollow (F i)*A.grace i
lemma bag(A:Dew V I)(F:V→ℂ)(i:Finset V): A.wrap F i=if A.mild i then ∏ j∈i,A.orts F j else 0:=by
 unfold wrap orts; split; rw [prod_mul_distrib]; congr 1; · induction i using Finset.induction_on with
   | empty=> rw [prod_empty,prod_empty]; exact Subtype.ext (one_smul ..)
   | insert x S k ih=> rw [prod_insert k,prod_insert k, ←hollowM, ih]; exact Set.Pairwise.mono (coe_subset.mpr (subset_insert ..)) ‹_› -- maybe mild irrelevant revert
 rfl
lemma choiceM (u:V→V→Prop)(A:Dew (Sigma f) I)(t: A.free=fun i j=> i.fst≠j.fst∧u i.fst j.fst)(S:Finset (Sigma f)): A.mild S ↔Smooth S∧(↑(down S):Set V).Pairwise u:=by
 constructor; intro h; constructor; · intro x hx y hy v; by_contra g; have he:= h hx hy g; rw [t] at he; exact he.1 v
 · intro x hx y hy v; obtain ⟨i,p,rfl⟩:= mem_image.mp hx; obtain ⟨j,e,rfl⟩:= mem_image.mp hy; have he:= h (show i∈ S from p) (show j∈ S from e) (fun t=>v (by rw [t])); rw [t] at he; exact he.2
 rintro ⟨k,h⟩ x hx y hy g; rw [t]; let T:=down S; have hp:x.1≠ y.1:=fun t=> g (k hx hy t); exact ⟨hp,h (show x.1∈T from mem_image_of_mem _ hx) (show y.1∈T from mem_image_of_mem _ hy) hp⟩
lemma choiceP (u:V→V→Prop)(A:Dew (Sigma f) I)(t: A.free=fun i j=> i.fst≠j.fst∧u i.fst j.fst)(F:Sigma f→ℂ): A.foldS F=∑ i:Finset V, if (i:Set V).Pairwise u then ∏ j∈i,∑ k:f j,A.orts F ⟨j,k⟩ else 0:=by
 let W(i:Finset (Sigma f)):= if (↑(down i):Set V).Pairwise u then ∏ j∈i,A.orts F j else 0; have he(i:Finset (Sigma f)): A.wrap F i=if Smooth i then W i else 0:=by rw [bag,choiceM u A t]; unfold W; by_cases g:Smooth i<;>simp [g]; -- shadow
 unfold foldS; simp_rw [he]; rw [sumDown]; apply sum_congr rfl; intro i _; by_cases h:(i:Set V).Pairwise u; · rw [if_pos h,lifted]; apply sum_congr rfl; intro j u; unfold W; rw [(mem_span _ _).mp u|>.2, if_pos h]
 rw [if_neg h,sum_eq_zero]; intro j u; unfold W; rw [(mem_span _ _).mp u|>.2,if_neg h]
theorem allTerms(A:Dew V I)(F:V→ℂ)(h:∀ i j,A.free i j): (∏ i, (A.orts F i+1))=A.foldS F:=by rw [Fintype.prod_add]; apply sum_congr rfl; intro i _; rw [A.bag,if_pos (show A.mild i from fun _ _ _ _ _=>h ..)]; simp
lemma orts_nil(A:Dew V I)(F:V→ℂ)(i:V)(v:A.line i≠[]): (A.orts F i)^2=0:=by
 obtain ⟨j,h⟩:= List.exists_mem_of_ne_nil _ v; rw [orts,mul_pow, show A.grace i^2=0 from ?_,mul_zero]; rw [pow_two]; exact Subtype.ext (word_blank _ _ j h h)
lemma little {A:Dough I}(p:A^2=0): exp A=A+1:=by
 rw [exp_eq_tsum ℝ]; dsimp only; rw [tsum_eq_sum (s:=range 2)]; norm_num [Finset.sum_range_succ,add_comm]; intro i hi; rw [mem_range] at hi; rw [pow_eq_zero_of_le (not_lt.mp hi) p,smul_zero]
theorem eTerm (A:Dew V I)(F:V→ℂ)(h:∀ i j,A.free i j)(u:∀ i,A.line i≠[]): exp (∑ i,A.orts F i)=A.foldS F:=by
 letI : NormedAlgebra ℚ (Dough I):=NormedAlgebra.restrictScalars ℚ ℝ (Dough I); rw [exp_sum,← allTerms _ F h]; apply prod_congr rfl; intro i _; exact little (A.orts_nil F i (u i))
-- all choices mutually free across sites. variant allow predicate gate bypass outside reading sites
lemma groups (A:Dew (Sigma f) I)(t:∀ i j,A.free i j ↔ i.fst≠ j.fst)(F:Sigma f→ℂ): A.foldS F=∏ i, (1+∑ j:f i,A.orts F ⟨i,j⟩):=by
 rw [A.choiceP (u:=fun _ _=>True) (by ext i j; simp [t]) F]; simp_rw [show ∀ i:Finset V,(i:Set V).Pairwise fun _ _=>True from fun _ _ _ _ _ _=> trivial]; simp_rw [add_comm (1:Dough I),ite_true]; rw [Fintype.prod_add]; simp
end YM.CF.BProof.Crystal.Dew

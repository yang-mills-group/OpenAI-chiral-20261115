import YM.CF.BPress.Palmer.Limousine
import YM.CF.BPress.Pine.Reel
/- Algebra for packing all polynomial choices, including the unique scalar term family in fuel. Calls Pine pricing, optional Y released on force uses only by outer phase. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Vesper
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Push.AbsoluteSums Gas Palmer Fock Pastry
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical
variable {I J K: Type*}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{Y : Type*}[AddCommMonoid Y]
section
lemma dual_sum (F:Finset (I⊕J)→Y) : ∑ p, F p=∑ p:Finset I,∑ q: Finset J,F (p.disjSum q):=by
 rw [← Fintype.sum_prod_type (f:=fun x:Finset I × Finset J=> F (disjSum x.1 x.2))]; apply Fintype.sum_equiv Finset.sumEquiv.toEquiv _ _; intro i; exact congrArg _ toLeft_disjSum_toRight.symm -- tune
variable (R:I→ I→Prop)(S:J→J→Prop)
def sumR (i j:I⊕J) : Prop:= Sum.elim (fun a=>Sum.elim (R a) (fun _=>False) j) (fun b=>Sum.elim (fun _=>False) (S b) j) i
lemma dual_rule (p:Finset I)(q:Finset J) : separated (sumR R S) (p.disjSum q) ↔ separated R p ∧ separated S q:=by
 constructor; intro g; exact ⟨fun i v j t e=>g _ (inl_mem_disjSum.mpr v) _ (inl_mem_disjSum.mpr t) (Sum.inl_injective.ne e),fun i v j t e=>g _ (inr_mem_disjSum.mpr v) _ (inr_mem_disjSum.mpr t) (Sum.inr_injective.ne e)⟩; rintro ⟨a,b⟩ (i|i) v (j|j) t e h; · exact a _ (inl_mem_disjSum.mp v) _ (inl_mem_disjSum.mp t) (fun z=> e (congrArg Sum.inl z)) h
 · exact h
 · exact h
 exact b _ (inr_mem_disjSum.mp v) _ (inr_mem_disjSum.mp t) (fun z=>e (congrArg Sum.inr z)) h
end
section
variable [CommSemiring K](R:I→I→Prop)(X:I→K)
def tin(p:Finset I):K:= if separated R p then ∏ i∈p,X i else 0
def box:=∑ p:Finset I,tin R X p
def silence(I:Type*) := fun (_ _: I)=>False
lemma wall : box (silence I) X = ∏ i,(1+ X i):=by
 rw [prod_one_add]; unfold box; apply sum_congr rfl; intro p _; exact if_pos (fun _ _ _ _ _=>not_false_eq_true ▸ trivial) -- tune
lemma hat(p:Finset I)(s:Finset J)(S:J→J→Prop)(V:J→K): tin (sumR R S) (Sum.elim X V) (p.disjSum s)=tin R X p*tin S V s:=by
 unfold tin; rw [dual_rule,prod_disjSum]; by_cases u:separated R p<;> by_cases v:separated S s <;> simp only [u,v, ↓reduceIte,and_self,and_false,false_and, Sum.elim_inl, Sum.elim_inr, mul_zero, zero_mul]
lemma kit(S:J→ J→Prop)(V:J→K): box R X * box S V=box (sumR R S) (Sum.elim X V):=by unfold box; rw [sum_mul,dual_sum]; apply sum_congr rfl; intro i _; rw [mul_sum]; simp_rw [hat]
variable (A:J→I)
abbrev mix (a b:J):= A a=A b ∨ R (A a) (A b) -- base clash always excluded
lemma order_rule (t:Finset J) : separated (mix R A) t↔ Set.InjOn A (t:Set J) ∧ separated R (t.image A):=by
 constructor; intro h; refine ⟨fun i v j p e=> by_contra (fun f=>h i v j p f (.inl e)),?_ ⟩; intro i v j p e f; obtain ⟨x,u,rfl⟩:= mem_image.mp v; obtain ⟨y,w,rfl⟩:= mem_image.mp p; exact h x u y w (fun g=> e (congrArg A g)) (.inr f)
 rintro ⟨b,h⟩ i v j p e (l|l); exact e (b v p l); exact h (A i) (mem_image_of_mem _ v) (A j) (mem_image_of_mem _ p) (fun t'=>e (b v p t')) l
lemma prepared (U:J→K)(h:∀ i,X i=∑ j∈ tribe A i,U j)(t:Finset I): tin R X t=∑ p∈Assembly A t,tin (mix R A) U p:=by
 by_cases u:separated R t
 · rw [tin,if_pos u, salon A U X h]; apply sum_congr rfl; intro p y; exact (if_pos ((order_rule ..).mpr ⟨(mem_filter.mp y).2.2, (blocks _ _ _ y).symm ▸ u⟩)).symm -- tune
 rw [tin,if_neg u]; symm; apply sum_eq_zero; intro p q; exact if_neg (fun v=>u (blocks _ p _ q ▸ ((order_rule ..).mp v).2)) -- tune
lemma release (U:J→K)(h:∀ i,X i=∑ j∈ tribe A i,U j): box R X=box (mix R A) U:=by unfold box; simp_rw [prepared R X A U h]; rw [collectMe,sum_subset (filter_subset ..)]; intro i u v; exact if_neg (fun t=>v (mem_filter.mpr ⟨u,(order_rule ..|>.mp t).1⟩))
lemma box_zero : box R (fun _ : I => (0:K))=1:=by unfold box; rw [sum_eq_single ∅]; simp [tin,separated]; intro b _ e; rw [tin]; split; exact prod_eq_zero (nonempty_iff_ne_empty.mpr e).choose_spec rfl; rfl; simp -- tune
end
end YM.CF.BPress.Vesper

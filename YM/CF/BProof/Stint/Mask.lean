import YM.CF.BProof.Stint.Earn

/-! Operator comparison on qualifying *input columns* of field arguments in common Stage.
Connectivity & variation, buying fixed threshold on reach. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Stint
open Function Filter Fock Finset Branch
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I Y Z G:Type*}[Fintype I][Fintype Y][DecidableEq I][DecidableEq Y]{b:Stage Y I Z G}
lemma stripPaid [Nonempty I] (b:Stage Y I Z G)(S : Seal Y): ‖strip b S‖≤1:= (cutM_idp _).norm_le _
lemma stripCheap [Nonempty I] (b:Stage Y I Z G)(S : Seal Y)(A:Op I) : ‖A * strip b S‖≤‖A‖:=(norm_mul_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) (stripPaid ..))
lemma strip_low {S T:Seal Y}(h:S⊆T):strip b T *strip b S= strip b S:=by
 ext i j; rw [stripL]; split; rfl; rename_i q; rw [←mul_one (strip b S),stripL,if_neg (fun t=>q (h t))]
lemma strip_low_norm [Nonempty I]{S T:Seal Y}(h:S⊆T)(A:Op I): ‖A * strip b S‖≤ ‖A*strip b T‖ := (le_of_eq (by rw [mul_assoc,strip_low h] : ‖A*strip b S‖=‖(A*strip b T)*strip b S‖)).trans (stripCheap ..)
lemma stripFrame (s:Tag b)(g:G)(S:Seal Y):Commute (strip b S) (s.run g).val :=strip_tag ..
variable [TopologicalSpace Z]{s t:Tag b}{P: Seal Y→ Raw Z I}{W: Seal Y → Toll I}{A:Raw Z I}{p:Pay} {x y:Z}(u:∀ S, Ticket s t S (W S) (P S))(L:Ledger p.rate W p.cash)(v:∀ x, A x=∑ S,P S x)

def tailPay (p:Pay)(r:ℕ):= Real.exp (-p.rate/2*r)*p.cash
include u L
lemma tailEarn (v:∀ x,A x=∑ S,P S x)(r:ℕ)(x:Z) : ‖A x - lop P r x‖≤tailPay p r :=(lip_tail P W u L v p.charge.le).boundOp (half_pos p.charge).le x
lemma lop_contained (k:ℕ)(S:Seal Y){r:ℝ}(q:0≤r)(h:∀ z∈S,b.eval (bay b.F z k) x y≤r): ‖(lop P k x-lop P k y)*strip b S‖≤r*p.cash :=by
 apply schur (fun i j=>r*saleM p.rate W i j) _ _ (mul_nonneg q p.funding.le); swap; · intro i; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (L.rows i) q
 swap; · intro j; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (L.cols j) q
 intro i j; rw [stripR]; split; swap; next e=> rw [norm_zero]; exact mul_nonneg q (sale_nn (fun i j k=>(u i).nonn j k) ..)
 next e=>
 rw [Matrix.sub_apply,lop,lop,Matrix.sum_apply,Matrix.sum_apply,←sum_sub_distrib]; refine (norm_sum_le ..).trans ?_
 have he(T:Seal Y)(t:T∈ ch Y k): ‖P T x i j - P T y i j‖ ≤ r*(rent p.rate T * W T i j):=by
    let U:= (u T).expo i j; apply (U.variation x y).trans; by_cases f:W T i j=0; rw [f,zero_mul,mul_zero,mul_zero]; obtain ⟨z,hz,g⟩:= U.triggered f; rw [mul_comm (W ..)]; apply mul_le_mul ((b.includeV ((z.basin g).trans (by intro d v; exact (bay_mem _).mpr (((bay_mem _).mp v).trans ((mem_filter.mp t).2.le)))) x y).trans (h _ e)) (le_mul_of_one_le_left U.positive (rent_one p.charge.le _)) U.positive q -- tune
 apply (sum_le_sum he).trans; rw [saleM, mul_sum]; exact sum_le_sum_of_subset_of_nonneg (ch Y k).subset_univ (fun i _ _=>mul_nonneg q (mul_nonneg (rent_pos _ _).le ((u i).nonn ..)))
omit u L in
lemma cap_compare [Nonempty I] (H:Earn p s t A)(k:ℕ)(S:Seal Y){r:ℝ}(q:0≤r)(h:∀ z∈S,b.eval (bay b.F z k) x y≤r): ‖(A x - A y)*strip b S‖ ≤ 2*tailPay p k + r*p.cash :=by
 obtain ⟨P,W,hp,L,v⟩:=H.holds
 let D:=lop P k
 rw [show A x-A y=(A x-D x)-(A y-D y)+(D x-D y) by abel]
 rw [add_mul,sub_mul ((A x)-_)]
 refine (norm_add_le ..).trans (add_le_add ((norm_sub_le ..).trans ((add_le_add ((stripCheap b _ _).trans (tailEarn (p:=p) hp L v k x)) ((stripCheap b _ _).trans (tailEarn (p:=p) hp L v k y))).trans_eq (two_mul _).symm)) (lop_contained hp L k S q h))
omit u L in
theorem tailPaid (p:Pay): Tendsto (tailPay p) atTop (𝓝 0) := by
 unfold tailPay; let r:=Real.exp (-p.rate/2); have he:0<r:=Real.exp_pos _; have hr:r<1:= Real.exp_lt_one_iff.mpr (by linarith [p.charge]); simp_rw [mul_comm (-p.rate/2), Real.exp_nat_mul]; simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one he.le hr).mul_const p.cash
end YM.CF.BProof.Stint

import YM.CF.BProof.Bias.Range
import YM.CF.BProof.Align.Hil
/-! Near-block-only translation rigidity at B-nogapz. Keep all operators L2;
no dimension losses. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Bias
open Function Filter Fock Finset Branch Stint Lattice Cube Align
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}{I:Type}[Fintype I][DecidableEq I][Nonempty I](F:I→Per N){r t:ℕ}{A B:Op I}
def swipe (k:Per N)(A:Op I): Op I:=∑ x:Per N,slice F x*A*slice F (x+k)
lemma swiped(k:Per N)(A:Op I)(i j) : swipe F k A i j= if k=F j-F i then A i j else 0:=by
 unfold swipe; rw [Matrix.sum_apply,sum_eq_single (F i),timeS,timeL,if_pos (mem_singleton_self _)]; simp only [slice,mem_singleton]; by_cases g:k=F j-F i
 · simp [g]
 have hh:F j≠F i+k:=fun p=> g (by rw [p,add_sub_cancel_left]); simp [hh,g]
 intro x _ h; rw [timeS,timeL,if_neg (fun t=>h (mem_singleton.mp t).symm)]; simp
 simp
lemma sliced(k x:Per N)(A:Op I): slice F x*swipe F k A= slice F x*A*slice F (x+k):=by
 ext i j; rw [timeL,timeS,timeL,swiped]; simp only [mem_singleton]; split; next h=> simpa [h,eq_sub_iff_add_eq,add_comm,eq_comm (a:=F j)] -- tune
 split <;> rfl
lemma swipe_sub (k:Per N)(A B:Op I): swipe F k A-swipe F k B=swipe F k (A-B):=by ext i j; simp only [Matrix.sub_apply,swiped]; split <;> simp
lemma sum_slice (x:Ket I): ∑ q:Per N,‖acts (slice F q) x‖^2=‖x‖^2:=by
 simp_rw [EuclideanSpace.norm_sq_eq]; rw [sum_comm]; apply sum_congr rfl; intro i _; simp only [slice,timeR,show ∀ S:Finset I,(acts (cutM S) x) i = _ from fun _=>cut_apply _ _ _,mem_filter]; simp [apply_ite ((‖·‖):ℂ→ℝ), apply_ite ((·^2):ℝ→ℝ)]
variable {K:ℝ}
lemma swipe_small (c:0≤K)(k:Per N)(A:Op I)(h:∀ x:Per N,‖slice F x*A*slice F (x+k)‖≤K): ‖swipe F k A‖≤K:=by
 let S:=swipe F k A; apply norm_bound_act c; intro x; apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1; rw [←sum_slice F,mul_pow,←sum_slice F x]
 let g(r:Per N):=‖acts (slice F r) x‖; apply le_trans (b:=∑ r:Per N,(K*g (r+k))^2) (sum_le_sum (fun i _=>?_))
 · simp_rw [mul_pow]; rw [← mul_sum]; exact le_of_eq (congrArg (fun x:ℝ=>K^2*x) (Equiv.sum_comp (Equiv.addRight k) (fun i=>g i^2)))
 apply pow_le_pow_left₀ (norm_nonneg _); rw [← act_mul,sliced]; let T:=slice F i * A; let D:=slice F (i+k); change ‖acts (T*D) x‖≤_; have he:T*D*D=T*D:=by rw [mul_assoc,(timeR_proj ..).isIdempotentElem]
 apply (le_of_eq (congrArg (‖·‖) ?_)).trans ((actuarial (T*D) (acts D x)).trans (mul_le_mul_of_nonneg_right (h i) (norm_nonneg _))); rw [←act_mul,he]
lemma timeLB(S)(A:Op I): ‖timeR F S * A‖ ≤ ‖A‖:= (norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) ((timeR_proj ..).norm_le _))
lemma timeUB(S)(A:Op I): ‖A*timeR F S‖ ≤ ‖A‖:= (norm_mul_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) ((timeR_proj ..).norm_le _))
lemma swipe_bill(k:Per N)(A:Op I): ‖swipe F k A‖≤ ‖A‖:= swipe_small F (norm_nonneg _) _ _ (fun i=> le_trans (timeUB ..) (timeLB ..))
lemma swipe_smr (k:Per N)(c:ℂ)(A:Op I): c • swipe F k A= swipe F k (c • A):=by ext i j; simp only [swiped,Matrix.smul_apply]; split; rfl; simp -- tune no SUnit
lemma Span.swipe {F:I→Per N}(h:Span F r A) : ∑ k∈ cent (0:Per N) r, swipe F k A=A:=by
 ext i j; rw [Matrix.sum_apply]; simp_rw [swiped]; rw [sum_ite_eq']; split; rfl; rename_i t; exact (h i j (Nat.lt_of_not_ge (fun l=> t (by apply (cent_at ..).2; unfold delta1; rw [sub_zero]; change delta1 N (F j) (F i) ≤ _; rwa [d_sym])))).symm -- tune
end YM.CF.BProof.Bias

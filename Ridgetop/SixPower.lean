import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace Factory
open Function Real Finset WithLp
open scoped Matrix Topology RealInnerProductSpace BigOperators Classical
variable {I:Type*}[Fintype I]
-- power six inequality via ≥0.CS or scalar cruft. use each triple sum geometric bound
private lemma triple(a b c:ℝ): a^2*b^2*c^2 ≤ a^6+b^6+c^6:=by
 let x:= max (max (a^2) (b^2)) (c^2) -- parentheses
 rcases le_total (a^2) (b^2) with h|h
 all_goals skip
 rcases le_total (b^2) (c^2) with p|p
 · have hv:=mul_le_mul h p (sq_nonneg _) (sq_nonneg b); have hx:= mul_le_mul_of_nonneg_left (h.trans p) (sq_nonneg c); -- simplify use case with nlin plus
   have hp:=mul_le_mul (h.trans p) p (sq_nonneg _) (sq_nonneg _); nlinarith only [pow_nonneg (sq_nonneg a) 3,pow_nonneg (sq_nonneg b) 3,mul_le_mul_of_nonneg_right hp (sq_nonneg c)]
 · have hp:=mul_le_mul_of_nonneg_right h (sq_nonneg b); have hv:=mul_le_mul hp p (sq_nonneg c) (mul_nonneg (sq_nonneg b) (sq_nonneg b)); nlinarith only [pow_nonneg (sq_nonneg a) 3,pow_nonneg (sq_nonneg c) 3,hv]
 rcases le_total (a^2) (c^2) with p|p
 · have hp:=mul_le_mul p (h.trans p) (sq_nonneg _) (sq_nonneg _); nlinarith only [pow_nonneg (sq_nonneg a) 3,pow_nonneg (sq_nonneg b) 3,mul_le_mul_of_nonneg_right hp (sq_nonneg c)]
 · have hp:=mul_le_mul_of_nonneg_left h (sq_nonneg a); have hv:=mul_le_mul hp p (sq_nonneg c) (mul_nonneg (sq_nonneg a) (sq_nonneg a)); nlinarith only [pow_nonneg (sq_nonneg c) 3,pow_nonneg (sq_nonneg b) 3,hv]
lemma styles(x:EuclideanSpace ℝ I): ‖x‖^6≤ ((3:ℝ)*(Fintype.card I:ℝ)^2)*(∑ i:I, x i^6):=by
 let e:= ((Fintype.card I):ℝ)
 rw [show (6:ℕ)=2*3 from rfl,pow_mul,EuclideanSpace.real_norm_sq_eq,show (∑ i:I,x i^(2:ℕ))^ (3:ℕ)=_ from
   (show (∑ i:I,x i^ (2:ℕ))^(3:ℕ)=(∑ i:I,x i^2)*(∑ i:I,x i^2)*(∑ i:I,x i^2) from by ring)]; simp_rw [sum_mul,mul_sum,sum_mul]
 trace_state
 refine le_trans (sum_le_sum (s:=univ) (f:=fun i:I=> (∑ j:I,∑ k:I,x i^2*x k^2*x j^2)) (g:=fun i:I=> (∑ j:I,∑ k:I,(x i^6+x k^6+x j^6))) (fun i _=>sum_le_sum fun j _=> sum_le_sum fun k _=>triple (x i) (x k) (x j))) ?_; simp [sum_add_distrib,←mul_sum]; ring_nf; exact le_rfl
lemma expiry{A B:ℝ}(ha:0≤A)(hb:0≤B):A^4*B^2 + A^2*B^4 ≤3*(A^6+B^6):=by
 nlinarith only [triple A A B,triple B B A,pow_nonneg ha 6,pow_nonneg hb 6] -- triple A A -> 2a6+b6! sums ->3a!, use / case instead limit 3
#check styles
#print axioms styles
end Factory

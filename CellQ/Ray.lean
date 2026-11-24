import CellQ.First
set_option autoImplicit false
set_option linter.flexible false
noncomputable section
namespace YM.CF.Drift
namespace Grain
open Function Finset Mew
open scoped BigOperators Topology
variable {I E:Type}[Fintype I][LinearOrder I][AddCommGroup E][Module ℂ E]
local notation "nT" => (Fintype.card (PairKey I)+1)
local notation "K"=> Key (PairKey I)
attribute [-instance] instDecidableEqLex
variable {cost:E→ℝ}{α:Type}[DecidableEq α] (S:Finset α)(w:α→ℝ)(D:α→Finset I)(F:α→Mew.Key (PairKey I)→E)
structure rateCost (κ:E→ℝ):Prop where
   low (x):0≤κ x
   zeroK :κ 0=0
   addK (x y):κ (x+y) ≤ κ x+ κ y
   scaleK (s:ℂ)(x):κ (s • x) = ‖s‖*κ x
lemma rateCost.sumK (h:rateCost cost)(S:Finset α)(f:α→E) :cost (∑ i∈S,f i)≤∑ i∈S,cost (f i):=by
 classical
 induction S using Finset.induction_on with
 | empty=> simp [h.zeroK]
 | insert i s v ih=> rw [sum_insert v,sum_insert v]; exact (h.addK ..).trans (add_le_add le_rfl ih)
lemma rainbow_batch (hp:rateCost cost)(fp:∀ i∈S,0≤w i){M:ℝ}{z:K}(h:∀ t:ℂ,‖t‖ ≤ 1 → ∑ i∈S,w i*cost (F i (t • z))≤ M)(k:ℕ): ∑ i∈S,w i*cost (rainbow (F i) z k)≤ M:=by
 let W:=lights nT; let a(i:α)(j:ℕ):=F i (W^j • z)
 let c:= ((nT:ℕ):ℝ)
 have hc:0<c:=by unfold c; positivity
 have he(i:α): cost (rainbow (F i) z k)≤ c⁻¹* ∑ j∈range nT,cost (a i j):=by
    unfold rainbow; rw [hp.scaleK,norm_inv,Complex.norm_natCast]; apply mul_le_mul_of_nonneg_left _ (by positivity); refine (hp.sumK _ _).trans (le_of_eq ?_); apply Finset.sum_congr rfl; intro j _; rw [hp.scaleK,norm_inv,norm_pow,norm_pow,light_one (show 0<nT by omega),one_pow,one_pow,inv_one,one_mul]
 apply (sum_le_sum (s:=S) (fun i hi=>mul_le_mul_of_nonneg_left (he i) (fp i hi))).trans
 conv_lhs=> arg 2; ext i; rw [mul_left_comm _ c⁻¹, Finset.mul_sum]
 rw [←Finset.mul_sum,sum_comm (s:=S)]
 calc
  c⁻¹ * _ ≤ c⁻¹ * (∑ _j∈ range nT, M):=by
      apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr hc).le; apply sum_le_sum; intro i _; unfold a; exact h _ (by rw [norm_pow,light_one (show 0<nT by omega),one_pow])
  _ = M:=by rw [sum_const,card_range,nsmul_eq_mul]; exact inv_mul_cancel_left₀ hc.ne' _

lemma paid_order (hp:rateCost cost)(fp:∀ i∈S,0 ≤ w i)(hg:∀ i∈S,Grain (D i) (F i)) (z:K){M:ℝ}(h:∀ t:ℂ,‖t‖ ≤ 1 → ∑ i∈S,w i *cost (F i (t • z)) ≤ M)(k:ℕ)(ht:k<nT)(v:α→ℝ)(A:ℝ)(u:0≤A)(L:∀ i∈S,k ≤ (D i).card→v i ≤A*w i) : ∑ i∈S,v i*cost (rainbow (F i) z k) ≤ A*M:=by
 apply le_trans _ (mul_le_mul_of_nonneg_left (rainbow_batch S w F hp fp h k) u)
 rw [mul_sum]; apply sum_le_sum; intro i hi; rw [←mul_assoc]; by_cases hf:k ≤ (D i).card
 · exact mul_le_mul_of_nonneg_right (L i hi hf) (hp.low _)
 rw [shawl_zero (hg _ hi) z ht (lt_of_not_ge hf),hp.zeroK,mul_zero,mul_zero]
end Grain
end YM.CF.Drift

import Mathlib
set_option autoImplicit false
set_option synthInstance.maxSize 18000
set_option maxHeartbeats 210000
noncomputable section
namespace Acacia
open Filter Function Finset Set
open scoped Topology NNReal BigOperators Classical ComplexConjugate
def hop (i:ℕ):ℝ:= (1/2)^i
lemma hop_pos(i:ℕ):0<hop i:=by unfold hop; positivity
lemma hop_tends:Tendsto hop atTop (𝓝 0):= tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
/-- fits growth n difference. -/
lemma signedE(C:ℝ)(h:0<C)(n:ℕ): ∃ c:ℝ,0<c∧∀ i,0 < i → C*(2/hop i)^n ≤ c^i:=by
 let A:=max 1 (C*2^n)
 refine ⟨A*2^n,mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left ..)) (by positivity),fun i hi=>?_⟩
 rw [mul_pow]
 have he:(2:ℝ)/hop i=2*2^i:=by unfold hop; rw [div_pow,one_pow,div_div_eq_mul_div,div_one]
 rw [he,mul_pow,←mul_assoc,←pow_mul, mul_comm i n,pow_mul]
 exact mul_le_mul_of_nonneg_right ((le_max_right ..).trans ((pow_le_pow_right₀ (le_max_left ..) (Nat.one_le_of_lt hi)).trans' (pow_one A).symm.le)) (by positivity)
lemma diffEra(C:ℝ)(h:0<C):∀ᶠ i:ℕ in atTop,C*hop i ≤ (3/4:ℝ)^i:=by
 let z:ℝ:=2/3
 have ht:Tendsto (fun i:ℕ=> C*z^i) atTop (𝓝 0):=mul_zero C ▸ (tendsto_pow_atTop_nhds_zero_of_lt_one (r:=z) (by norm_num [z]) (by norm_num [z])).const_mul C
 filter_upwards [ht.eventually (ge_mem_nhds zero_lt_one)] with i e;
 calc C*hop i=C*z^i*((3/4:ℝ)^i):=by rw [mul_assoc,←mul_pow]; unfold hop z; norm_num
      _ ≤ _:=le_trans (mul_le_mul_of_nonneg_right e (by positivity)) (le_of_eq (one_mul _))
#print axioms signedE
#print axioms diffEra
end Acacia

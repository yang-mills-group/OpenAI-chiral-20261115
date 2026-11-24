import Preen.Burden
set_option autoImplicit false
noncomputable section
namespace YM.Preen
open Real Function Filter
open scoped Topology
lemma shore_high(L:ℝ)(h:1≤L):∀ (b:ℕ),∃ A:ℕ,∀d:ℕ, L^(b*d^2) ≤ shoreH d^A:=by
 obtain ⟨K,hK⟩:= exists_nat_gt (log L); have hL:0<L:=zero_lt_one.trans_le h
 refine fun b=>⟨b*K,fun d=>?_⟩
 have hb:=exp_log hL
 conv_lhs=> rw [←hb,←Real.exp_nat_mul]
 unfold shoreH; rw [←Real.exp_nat_mul,Real.exp_le_exp]; push_cast
 have hk':= mul_le_mul_of_nonneg_left hK.le (show 0≤(b:ℝ)*(d:ℝ)^2 by positivity); linarith only [hk']
lemma tripleH : ∀ᶠ d:ℕ in atTop, (2:ℝ)^d ≤ shoreH d:=by
 filter_upwards [eventually_ge_atTop (1:ℕ)] with d h
 conv_lhs=> rw [←exp_log (show 0<(2:ℝ) from two_pos), ←Real.exp_nat_mul]
 unfold shoreH; rw [Real.exp_le_exp]; have hu:(1:ℝ) ≤ d:=by exact_mod_cast h
 nlinarith only [hu,twoAlarms.2]
lemma heavy_cut {L A:ℝ}{Λ:ℕ→ℝ}(l:1≤L) (a:∀ᶠ d in atTop,0≤Λ d ∧ Λ d ≤ shoreH d^10)(b:0≤ A) :
 ∀ᶠ d:ℕ in atTop, let k:ℕ:=64*d^2; let R:= L^k*Λ d; ((((2:ℝ)/(64*L^4))^k*(2^d*A))*R^4*(shoreH d)^9) ≤1:=by
 have hb0 : 0 < L:= zero_lt_one.trans_le l
 filter_upwards [shore_up.eventually_gt_atTop A,a,tripleH] with d h e hr k R
 -- factor ((1/32)^k) * Λ^4 * ..
 have hf: (32:ℝ)⁻¹ ^k ≤ (shoreH d^64)⁻¹:=by
    have hz: shoreH d ^64 ≤ (32:ℝ)^k:=by
       have h':1≤ log 32:=by rw [show (32:ℝ)=(2:ℝ)^5 from (by norm_num),Real.log_pow]; norm_num; linarith only [twoAlarms.1]
       conv_rhs=>rw [←exp_log (show 0<(32:ℝ) by norm_num),← Real.exp_nat_mul]
       unfold shoreH; rw [←Real.exp_nat_mul,Real.exp_le_exp]; unfold k; push_cast; nlinarith only [mul_le_mul_of_nonneg_left h' (show 0 ≤(d:ℝ)^2 from sq_nonneg _)]
    rw [inv_pow]; exact (inv_le_inv₀ (pow_pos (by norm_num) _) (pow_pos ((zero_lt_one.trans_le (shore_paid _))) _)).mpr hz
 have hx: ((((2:ℝ)/(64*L^4))^k)*R^4)=(32:ℝ)⁻¹^k*(Λ d)^4:=by
    unfold R; rw [mul_pow,←pow_mul, Nat.mul_comm k 4,pow_mul L 4 k,←mul_assoc,←mul_pow,show 2/(64*L^4)*L^4=(32:ℝ)⁻¹ from (by field)]
 let Z:=shoreH d; have hg:1 ≤ Z:=shore_paid _
 rw [show ((((2:ℝ)/(64*L^4))^k*(2^d*A))*R^4*Z^9)= ((((2:ℝ)/(64*L^4))^k)*R^4)*(2^d*A)*Z^9 from (by ring),hx]
 have h0:0<Z:=zero_lt_one.trans_le hg
 calc
   _ ≤ (Z^64)⁻¹ *(Z^10)^4*(Z*Z)*Z^9:= by gcongr <;> first | exact hf | exact hr | exact h.le | exact e.2 | positivity | exact e.1 | trace_state; fail
   _ ≤ _:= by
     field_simp
     exact one_le_pow₀ hg
end YM.Preen

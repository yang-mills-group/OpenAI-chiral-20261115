import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower -- lightweight separated
open Function Set Filter Metric
open scoped Topology NNReal Classical
namespace GrowthClock
variable (f:ℕ→ℝ)(p: ℕ)(m: ℝ)
variable (T:ℝ)(h:∀ s:ℕ,p≤ s→ f s ≤ ((1/2:ℝ)^(s-p))*T) (t:Tendsto f atTop (𝓝 0))(w:1≤ m)(v:0<T)
include h t v w
theorem window :∃ C:ℝ,0<C∧∃ n:ℕ,∀ δ:ℝ,0<δ→δ≤1→∃ s:ℕ,p≤ s∧ f s≤δ∧ m^s ≤ C/δ^n:=by
 obtain ⟨n,hn⟩:=(tendsto_pow_atTop_atTop_of_one_lt (r:= (2:ℝ)) one_lt_two).eventually (eventually_ge_atTop m) |>.exists; change m ≤ (2:ℝ)^n at hn
 let u:= m^p; let c:=m^(p+1)*T^n; have hc:0<c:=by unfold c; positivity
 refine ⟨u+c,(by unfold u; positivity),n, fun δ q e=>?_⟩
 obtain hK : ∃ s:ℕ,p≤ s ∧ f s≤δ:= ((eventually_ge_atTop p).and (t.eventually (ge_mem_nhds q))).exists; let s:= Nat.find hK
 refine ⟨s,(Nat.find_spec hK).1,(Nat.find_spec hK).2,(le_div_iff₀ (pow_pos q _)).mpr ?_⟩; obtain k:(s=p)∨p<s:= Or.symm (lt_or_eq_of_le (show p≤ s from (Nat.find_spec hK).1))|>.imp Eq.symm id -- syntax or
 rcases k with k|k; · rw [k]; exact (mul_le_of_le_one_right (by positivity) (pow_le_one₀ q.le e)).trans (le_add_of_nonneg_right hc.le)
 let d:=s-1; have hb:d<s:=by omega
 have hu:p≤d:=by omega
 let α:=d-p; have he:δ< ((1/2:ℝ)^α)*T:= (lt_of_not_ge (fun u=> Nat.find_min hK (m:=d) hb ⟨hu,u⟩)).trans_le (h d hu)
 have ht:δ^n ≤ ((1/2:ℝ)^n)^α*T^n:= by rw [←pow_mul,Nat.mul_comm,pow_mul,←mul_pow]; exact pow_le_pow_left₀ q.le he.le n
 have hz:m^s=m^(p+1)*m^α:=by nth_rw 1 [show s=p+1+α from (by omega)]; exact pow_add ..
 calc
    _ ≤ (m^(p+1)*(2^n:ℝ)^α)*(((1/2:ℝ)^n)^α*T^n):=by rw [hz]; apply mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans w) hn _) (by positivity)) ht <;> positivity
    _=c:= by
        rw [one_div, inv_pow (2:ℝ),inv_pow ((2:ℝ)^n)]; unfold c; generalize_proofs; field_simp
    _≤ _:=le_add_of_nonneg_left (pow_nonneg (by positivity) _)
#print axioms window
end GrowthClock
end YM.CF.Buffered.Afterglow.Tower

import YM.CF.BProof.Grid.Half

/-! Fixed choices *before* angle widths. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Grid.Blend
open Function Lattice Filter
open scoped Topology BigOperators

def speed (P b : ℝ)(k:ℕ) : ℝ := (2*P-P/(2:ℝ)^k)/(b*2^k)
theorem speed_le {P b:ℝ}(hp:0<P)(hb:0<b)(k:ℕ):0<speed P b k ∧ speed P b k ≤ 2*P/(b*2^k) := by
 have hp':0<(2:ℝ)^k:=by positivity
 have hv:1≤(2:ℝ)^k:=one_le_pow₀ (by norm_num); unfold speed; have hz : P/(2:ℝ)^k ≤ P:= div_le_self hp.le hv
 constructor; exact div_pos (by linarith) (by positivity)
 apply div_le_div_of_nonneg_right _ (by positivity); exact sub_le_self _ (by positivity)

structure Ticket (P C ε b u : ℝ) : Prop where
 pre : 0 < b
 mass : 0 < u
 small (k:ℕ): u/(b*2^(k+1))^2 + speed P b k≤ε
 bill (k:ℕ): speed P b k / 2 + C*(u/(b*2^(k+1))^2+(speed P b k)^2) ≤ speed P b (k+1)

lemma buys (P C ε:ℝ)(hp:0<P)(hc:0<C)(he:0<ε) : ∀ᶠ b:ℝ in atTop, ∀ u:ℝ,0<u → u≤1 → Ticket P C ε b u:=by
 filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop ((1+2*P)/ε),eventually_ge_atTop ((C+16*C*P^2)/P)] with b hb hw hW u hu hp'
 have h : 0<b:=zero_lt_one.trans_le hb
 constructor
 · exact h
 · exact hu
 · intro k; have hy: 1≤(2:ℝ)^k:= one_le_pow₀ (by norm_num)
   have H: b≤(b*2^(k+1))^2:=by
      have hp:b≤ b*2^(k+1):= le_mul_of_one_le_right h.le (one_le_pow₀ (by norm_num)); nlinarith
   calc
     _ ≤ 1/b + 2*P/b:= add_le_add (by gcongr) ((speed_le hp h k).2.trans (by gcongr; exact le_mul_of_one_le_right h.le hy))
     _ ≤ _:=by rw [←add_div,div_le_iff₀ h]; linarith [(div_le_iff₀ he).mp hw]
 intro k
 let y:=(2:ℝ)^k; have hy:0<y:=by unfold y; positivity
 apply le_trans (add_le_add_right (mul_le_mul_of_nonneg_left (add_le_add (div_le_div_of_nonneg_right hp' (sq_nonneg _)) (pow_le_pow_left₀ (speed_le hp h k).1.le (speed_le hp h k).2 2)) hc.le) _)
 unfold speed; rw [pow_succ]; change (2*P-P/y)/(b*y)/2+C*(1/(b*(y*2))^2+(2*P/(b*y))^2) ≤ (2*P-P/(y*2))/(b*(y*2)); field_simp; linarith only [(div_le_iff₀ hp).mp hW]
end YM.CF.BProof.Grid.Blend

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option maxHeartbeats 200000
noncomputable section
namespace UnpadTicket
open Filter
open scoped Topology Classical
variable {s v z:ℕ}{d D C p:ℝ} {ℓ:ℕ→ℝ}{G:Type*}[NormedAddCommGroup G] {f:ℕ→ℝ→ℝ→G}
/-- Two-way estimate. Constants do not price individual v or individual s. -/
def Climbed (ℓ:ℕ→ℝ)(z:ℕ) (f:ℕ→ℝ→ℝ→G)(D C:ℝ):Prop:= ∀ s v:ℕ,z ≤ s→ z ≤ v→∀ l r:ℝ,ℓ (min s v)≤ l→ℓ (min s v) ≤ r→ ‖f v l r‖ ≤ C*D^s
private lemma geom_up {V:ℕ→G}{b:ℝ} (h:0≤ b)(f:∀ n, dist (V n) (V (n+1))≤ b*(1/2:ℝ)^n) : ∀ n:ℕ, ‖V n‖ ≤ ‖V 0‖+2*b*(1-(1/2:ℝ)^n):=by
 intro n; induction n with
 | zero=> simp
 | succ n a=> have l:= (norm_sub_norm_le (V (n+1)) (V n)).trans (show ‖V (n+1)-V n‖ ≤ b*(1/2:ℝ)^n from by rw [←dist_eq_norm, dist_comm]; exact f _); rw [pow_succ]; linarith only [l,a]
theorem climbing (hp:0 < p)(hd:1 ≤ d)(M:d/p ≤ 1/2) (C₀ C₁:ℝ)(q:0 ≤ C₀)(w:0 ≤ C₁) (A:∀ s v:ℕ,z ≤ s→ s ≤ v→ ℓ v ≤ ℓ s)
 (B:∀ v,z ≤ v → ∀ l r,ℓ v ≤ l→ℓ v ≤ r→‖f v l r‖ ≤ C₀*d^v)
 (R:∀ s v:ℕ,z≤s→s<v→∀ l r,ℓ s≤l→ℓ s≤r→ dist (f v l r) (f (v+1) l r) ≤ (C₁*d^v)*(p^(v-s))⁻¹):
 ∃ C:ℝ,0≤ C∧Climbed ℓ z f d C:=by
 have h:0< d:=zero_lt_one.trans_le hd; refine ⟨C₀*d+2*C₁*(d/p),by positivity,fun s v u a l r a₁ b₁=>?_⟩; by_cases c:s<v; swap; · rw [min_eq_right (by omega : v ≤ s)] at a₁ b₁; exact (B _ a _ _ a₁ b₁).trans (mul_le_mul (le_trans (le_mul_of_one_le_right q hd) (le_add_of_nonneg_right (by positivity))) (pow_le_pow_right₀ hd (by omega)) (pow_nonneg h.le _) (by positivity))
 rw [min_eq_left c.le] at a₁ b₁; let e:=C₁*d^s*(d/p); let U(n:ℕ):= f (s+1+n) l r
 let a' := le_trans u (Nat.le_succ s)
 have he(n:ℕ):dist (U n) (U (n+1)) ≤ e*(1/2:ℝ)^n:=by
    have hu:s+1+n-s=n+1:=by omega
    calc
       _ ≤(C₁*d^(s+1+n))*(p^(s+1+n-s))⁻¹:=R _ _ u (by omega) _ _ a₁ b₁ -- defEq nat
       _ = e*(d/p)^n:=by unfold e; rw [hu,pow_add d,pow_succ,pow_succ,mul_inv_rev,div_pow, ←inv_pow]; repeat' rw [div_eq_mul_inv]; ring -- rw issue
       _ ≤ _:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) M _) (by positivity)
 let n:= v-(s+1)
 have hu:v=s+1+n:=by unfold n; omega
 have t:=A s (s+1) u (Nat.le_succ _); have hv: ‖U 0‖ ≤ C₀*d^(s+1):= B _ a' _ _ (t.trans a₁) (t.trans b₁)
 calc ‖_‖=‖U n‖:= congrArg (fun k=> ‖f k l r‖) hu
      _≤_:= le_trans (geom_up (b:=e) (by positivity) he n) ?_
 rw [add_mul, show _* _=C₀*d^(s+1) from (by rw [pow_succ]; ring : C₀*d*d^s=C₀*d^(s+1)), show 2*C₁*(d/p)* d^s= 2*e from (by unfold e; ring)] -- wrong parentheses in show
 apply add_le_add hv; exact mul_le_of_le_one_right (by positivity) (sub_le_self _ (by positivity))
/- Choose integer exponent; no common numeric claim 20. Might later need small explicit depending growth vs rank degree. -/
theorem beaming (h:1 ≤ D) (q:0< ℓ z)(A: Tendsto ℓ atTop (𝓝 0))(B:∀ v:ℕ,z ≤ v→ ℓ v≤ (1/2:ℝ)^(v-z) * ℓ z): ∃ (k:ℕ)(C:ℝ), 0< C∧ ∀ t:ℝ,0<t→t≤1→∃ s:ℕ,z ≤ s ∧ ℓ s < t∧ t^k*D^s≤ C := by
 obtain ⟨k',U⟩:= ((tendsto_pow_atTop_atTop_of_one_lt (show (1:ℝ)<2 by norm_num)).eventually (eventually_ge_atTop D)).exists
 let C:= max (D^z) ((ℓ z)^k' * D^(z+1)); have l:0<D:=zero_lt_one.trans_le h; refine ⟨k',C,(pow_pos l _).trans_le (le_max_left ..),fun t e r=>?_⟩
 have hx:∃ s:ℕ,z ≤ s∧ℓ s < t:= ((eventually_ge_atTop z).and (A.eventually (gt_mem_nhds e))).exists; have ht:= Nat.find_spec hx; let s:=Nat.find hx; refine ⟨s,ht.1,ht.2,?_⟩; by_cases a:s=z; · rw [a]; exact (mul_le_of_le_one_left (by positivity) (pow_le_one₀ e.le r)).trans (le_max_left ..)
 let n:= s-(z+1); have f:s=z+n+1:=by change z ≤ s ∧ ℓ s<t at ht; unfold n; omega
 have hv:t ≤ ℓ (z+n):= le_of_not_gt (fun w=> Nat.find_min hx (show z+n < s from (by omega)) ⟨Nat.le_add_right ..,w⟩); have hp:= hv.trans (B (z+n) (Nat.le_add_right ..)); rw [Nat.add_sub_cancel_left] at hp
 let W:ℝ:=((1/2:ℝ)^n*ℓ z)^k'; have he:W* D^n≤(ℓ z)^k':=by
    refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ l.le U n) (by positivity : 0 ≤ W)).trans (le_of_eq ?_); unfold W; rw [mul_pow,←pow_mul,pow_mul',mul_right_comm,←mul_pow, ←mul_pow]; norm_num
 calc
    _ ≤ W* D^s:=mul_le_mul_of_nonneg_right (pow_le_pow_left₀ e.le hp _) (by positivity)
    _ = W * D^n * D^(z+1):=by
        conv_lhs => rhs; arg 2; rw [show s=z+1+n from (by omega)]
        rw [pow_add]; ring
    _ ≤ C:= (mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ D^(z+1))).trans (le_max_right ..)
#print axioms climbing
#print axioms beaming
end UnpadTicket

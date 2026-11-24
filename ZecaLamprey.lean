import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology


/-- sum suppressed even estimates. -/
lemma lampSeries {x K : ℝ} 
 (f:∀k:ℕ, x^(2*k)/(Nat.factorial (2*k))≤K)
 (b:ℝ) (bp:0≤b)(u:b<1):
 Real.exp (b*x) ≤ 2*((1-b^2)⁻¹ * K):= by
 calc
  _ ≤ 2*Real.cosh (b*x):=by rw [Real.cosh_eq];linarith only [Real.exp_pos (-(b*x))]
  _ ≤ _:=by
    gcongr
    apply hasSum_le _
       (Real.hasSum_cosh _) ((hasSum_geometric_of_lt_one (sq_nonneg b) (pow_lt_one₀ bp u
        (by decide : (2:ℕ)≠0))).mul_right K)
    intro k
    rw [mul_pow]
    change _ ≤ (b^2)^k*K
    rw [mul_div_assoc,pow_mul]
    exact mul_le_mul_of_nonneg_left (f k) (by positivity)
#check hasSum_le

/-- gap slope contradiction at infinity. -/
theorem lamprey (z E :ℝ) (a:0≤E) (l:E<z)
 (D:ℝ)
 (p:∀ t k:ℕ, (z*t)^(2*k)/(Nat.factorial (2*k))≤ D*Real.exp (E*t)):
 False :=by
 have y:0<z:=a.trans_lt l
 obtain ⟨b,w,bq⟩:=exists_between l
 have g:0<b:=a.trans_lt w
 have e(t:ℕ):=lampSeries (p t) (b/z) (by positivity) ((div_lt_one y).2 bq)
 obtain ⟨t,u⟩:=exists_nat_gt ((2*((1-(b/z)^2)⁻¹ * D)) / (b-E))
 have c:=e t
 rw [← mul_assoc (b/z),div_mul_cancel₀ b y.ne',
     show b*(t:ℝ)=(b-E)*t+E*t from by ring,Real.exp_add] at c
 conv_rhs at c =>
    rw [←mul_assoc (1 - (b / z) ^ 2)⁻¹,← mul_assoc]
 have i:=le_of_mul_le_mul_right c (Real.exp_pos _)
 have r:=Real.add_one_le_exp ((b-E)*t)
 have j:=(div_lt_iff₀ (sub_pos.mpr w)).mp u
 linarith only [i,j,r]
#print axioms lamprey

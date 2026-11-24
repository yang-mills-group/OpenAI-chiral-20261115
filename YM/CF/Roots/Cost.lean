import YM.CF.Roots.Coal
import YM.CF.Roots.Coal
import YM.CF.Roots.Coal
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 16000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Roots
open Function Finset Filter Metric MeasureTheory Lattice Lattice.Corona Wilson Precision Pressure RG
open Jet Fock Cube Lat Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
variable {n:Side}
-- enumeration of sample paths (Mark circle scripts pay steep mixed bond). R0 fixed root.
local notation "K"=> Site n
variable {d B m:ℕ}
lemma tear_r (C ε:ℝ)(i:ℕ)(he:0<ε) : ∀ᶠ n:ℕ in atTop,C*(n:ℝ)^i≤Real.exp (ε*n):=by
 have ht:= (Real.tendsto_exp_div_pow_atTop i).comp (tendsto_natCast_atTop_atTop (R:=ℝ) |>.const_mul_atTop he)
 filter_upwards [ht.eventually_ge_atTop (C/ε^i),eventually_ge_atTop 1] with n v p
 have hu:0<(n:ℝ):=by exact_mod_cast p
 change C/ε^i ≤ Real.exp (ε*n)/(ε*n)^i at v; rw [le_div_iff₀ (by positivity)] at v; rw [mul_pow,← mul_assoc, div_mul_cancel₀ C (by positivity)] at v; exact v
abbrev cape_B(m:ℕ):ℕ:=m^3
abbrev chip_B(B m:ℕ):ℕ:= m*(4*B+2)
lemma pearl_y(t:ℕ)(hv:0<t):pearl (t^3) ≤3^4*t^12:=by
 unfold pearl; have he:0 < t^3:=by positivity
 calc
    _ ≤ (3*t^3)^4:=Nat.pow_le_pow_left (by omega) _
    _ = _:=by ring
lemma pearl_m(u t:ℕ)(hu:0 < u)(p:u ≤ t):pearl (chip_B u t+u) ≤15^4*t^8:=by
 let v:= chip_B u t+u; have ht:4*u+2≤6*t:=by omega
 have hf:0 < t:=by omega
 have h:t≤t^2:=by nlinarith; -- ring polynomial
 have hp:v ≤ 7*t^2:=by have hv:= Nat.mul_le_mul_left t ht; unfold v chip_B; nlinarith
 unfold pearl; have ht:v+v+1≤15*t^2:=by omega
 exact (Nat.pow_le_pow_left ht 4).trans_eq (by ring)
lemma sev_B (u m:ℕ)(v:0<u): (chip_B u m / (u^3))*u ≤ 6*m:=by
 let t:= chip_B u m; let k:=t/u^3; have he:k*u^2 ≤ k*u^3:=Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega)); have hx:k*u^3≤ m*(4*u+2):=Nat.div_mul_le_self ..; have hp:4*u+2≤6*u:=by omega
 apply Nat.le_of_mul_le_mul_right _ v; refine (le_of_eq ?_).trans ((he.trans hx).trans ((Nat.mul_le_mul_left m hp).trans_eq (show m*(6*u)=6*m*u from by ring))) -- tune which lemma side
 unfold k t; ring -- cape_B not occurrence
variable (ε C:ℝ)(t:ℕ)(p:1 ≤ C)(hv:0<ε)
abbrev rentP (C:ℝ)(B m t:ℕ):ℝ:= (pearl (chip_B B m+B):ℕ)*(pearl (cape_B B):ℝ) ^(chip_B B m/cape_B B) * (2*C) ^ ((chip_B B m/cape_B B+1)*t)
abbrev Nice_B (B t:ℕ)(C ε:ℝ):Prop:=∀ m:ℕ, B ≤ m → rentP C B m t ≤ Real.exp (ε*m)
include p hv
lemma chill_K : ∀ᶠ B:ℕ in atTop,Nice_B B t C ε:=by
 let α:=ε/8; have hp:0<α:=by unfold α; positivity
 let KB:= (2*C)^t; have hz:0 ≤ KB:=by have ht:=zero_le_one.trans p; unfold KB; positivity
 obtain ⟨u,z⟩:=eventually_atTop.mp (tear_r ((15:ℝ)^4*KB) α 8 hp)
 filter_upwards [tear_r ((3:ℝ)^4*KB) α 12 hp,eventually_ge_atTop u,eventually_ge_atTop 1] with B v h ht m hw
 let k:=chip_B B m/cape_B B; let T:=pearl (chip_B B m+B); let W:= pearl (cape_B B); have hx:rentP C B m t=T*KB*((W:ℝ)*KB)^k:=by
    change (T:ℝ)*(W:ℝ)^k*(2*C)^((k+1)*t)=_; rw [Nat.mul_comm (k+1) t,pow_mul]
    change ↑T*(W:ℝ)^k*KB^(k+1)=_; rw [pow_succ,mul_pow]
    ring
 have ha: (T:ℝ)*KB≤ Real.exp (α*m):=by
    have hv':(T:ℝ)≤ (15:ℝ)^4*(m:ℝ)^8:=by exact_mod_cast pearl_m B m ht hw
    refine (mul_le_mul_of_nonneg_right hv' hz).trans ((by ring : (15^4*(m:ℝ)^8)*KB=15^4*KB*(m:ℝ)^8).trans_le (z m (le_trans h hw)))
 have hh: (W:ℝ)*KB≤Real.exp (α*B):=by
    have hp:(W:ℝ) ≤ (3:ℝ)^4*(B:ℝ)^12:=by exact_mod_cast pearl_y B ht
    refine (mul_le_mul_of_nonneg_right hp hz).trans ((by ring : (3^4*(B:ℝ)^12)*KB=3^4*KB*(B:ℝ)^12).trans_le v)
 have hy:= mul_le_mul ha (pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hz) hh k) (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hz) _) (Real.exp_pos _).le
 refine hx.trans_le (hy.trans ?_)
 have hK: (k:ℝ)* B≤ 6*(m:ℝ):=by exact_mod_cast sev_B B m ht
 rw [←Real.exp_nat_mul,←Real.exp_add]; apply Real.exp_monotone; calc
    _ = α*m+ α*((k:ℝ)*B):= by ring
    _ ≤ α*m+ α*(6*m):= add_le_add_right (mul_le_mul_of_nonneg_left hK hp.le) _ -- order
    _ ≤ _:=by unfold α; nlinarith [Nat.cast_nonneg (α:=ℝ) m]
end YM.CF.Roots

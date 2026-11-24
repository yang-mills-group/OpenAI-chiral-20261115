import YM.SU5.Exchange.Seed.Ticket
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
variable {t X:ℕ}{q z:ℝ}
def packF(C:ℝ)(B t:ℕ) :=∀ m:ℕ,B^2 ≤20*m → rentP C B m t≤ Real.exp ((m:ℝ)/B/4)
-- explicit eventual threshold even for `C ~ exp(.low B)`
lemma niceT (t:ℕ)(C:ℕ→ℝ)(v:∀ᶠ m:ℕ in atTop,1≤ C m ∧ (2*C m)^t≤ Real.exp ((m:ℝ)/10000)): ∀ᶠ m:ℕ in atTop, packF (C m) m t:=by
 let P(x:ℝ):=x/64
 have W(s:ℕ)(k:ℝ):∀ᶠ i:ℝ in atTop, k*i^s ≤ Real.exp (P i):=by
    let η:ℝ:=1/64; have hx:0<η:=by norm_num [η]
    let T:= (Real.tendsto_exp_div_pow_atTop s).comp ((tendsto_id (x:=Filter.atTop)).const_mul_atTop hx); filter_upwards [T.eventually_ge_atTop (k/η^s), eventually_gt_atTop 0] with i v h; change k/η^s ≤ Real.exp (η*i)/(η*i)^s at v; rw [le_div_iff₀ (by positivity), mul_pow,←mul_assoc, div_mul_cancel₀ _ (by positivity:η^s≠0)] at v; exact v.trans_eq (by congr 1; unfold η P; ring) -- parsing
 obtain ⟨u,g⟩:= eventually_atTop.mp (W 16 ((15:ℝ)^4*20^8)); let L(B:ℕ):ℝ:= (B:ℝ)/100
 have hT:Tendsto L atTop atTop:=by 
    apply Filter.tendsto_atTop.2; intro a; obtain ⟨m,h⟩:=exists_nat_gt (100*a); filter_upwards [eventually_ge_atTop m] with n hn; have hu:(m:ℝ)≤ n:=by exact_mod_cast hn
    unfold L; linarith
 filter_upwards [v,hT.eventually_ge_atTop u,hT.eventually (W 12 (3^4*100^12)), eventually_ge_atTop 20] with B v gB tB x m h
 let k:=chip_B B m/cape_B B; let T:=pearl (chip_B B m+B); let Q:=(2*C B)^t; let S:=pearl (cape_B B); let X:ℝ:=m; let Y:ℝ:=B
 have hN:Y≥20:= (by unfold Y; exact_mod_cast x); have hY:0<Y:=by linarith
 have h1: 0 ≤ X:=Nat.cast_nonneg _; have hx:Y^2 ≤ 20*X:=by unfold X Y; exact_mod_cast h
 have huQ:0 ≤ Q:=pow_nonneg (mul_nonneg (by norm_num) (by linarith only [v.1])) _
 have hW:20*(X/Y)^2≥X:=by field_simp; nlinarith only [mul_le_mul_of_nonneg_right hx h1]
 have hm:B≤ m:=by
    suffices h:Y≤X by exact Nat.cast_le.mp (show (B:ℝ)≤ (m:ℝ) from h)
    nlinarith [mul_le_mul_of_nonneg_right hN hY.le]
 have hv:rentP (C B) B m t=T*Q*((S:ℝ)*Q)^k:=by
    change (T:ℝ)*(S:ℝ)^k*(2*C B)^((k+1)*t)=_; rw [Nat.mul_comm (k+1) t,pow_mul]; change ↑T*(S:ℝ)^k*Q^(k+1)= _; rw [pow_succ,mul_pow]; ring
 have hp: L B ≤ X/Y:= (le_div_iff₀ hY).mpr (by change Y/100*Y ≤ _; nlinarith only [hx,h1])
 have hq:(S:ℝ) ≤ Real.exp (P (L B)):=by
    have hv:(S:ℝ) ≤3^4* (Y:ℝ)^12:=by unfold S Y; exact_mod_cast (pearl_y B (by omega))
    refine hv.trans (le_trans (le_of_eq ?_) tB); show 3^4*(Y:ℝ)^12=3^4*100^12* (L B)^12; change _=_*(Y/100)^12; ring -- check subst direction
 have he: (T:ℝ) ≤ Real.exp (P (X/Y)):=by
    have hv':(T:ℝ)≤ (15:ℝ)^4*(m:ℝ)^8:=by exact_mod_cast pearl_m B m (by omega) hm
    refine hv'.trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h1 hW 8) (by norm_num : (0:ℝ)≤15^4)).trans ?_)
    calc _ = (15^4*20^8)*(X/Y)^16:=by ring
         _ ≤ _:=g _ (le_trans gB hp)
 have hk:(k:ℝ)*Y ≤ 6* (X/Y):=by
    rw [←mul_div_assoc,le_div_iff₀ hY]; let T':= Nat.div_mul_le_self (chip_B B m) (cape_B B)
    have hv:k*B^3 ≤ m*(6*B):= T'.trans (Nat.mul_le_mul_left m (by omega)); have h0: (k:ℝ)*Y^3≤ X*(6*Y):=by unfold X Y; exact_mod_cast hv
    apply le_of_mul_le_mul_right _ hY; nlinarith only [h0]
 let V:ℝ:=Y/10000; have he': (T:ℝ)*Q≤Real.exp (P (X/Y)+V):= (mul_le_mul he v.2 huQ (Real.exp_pos _).le).trans_eq (Real.exp_add ..).symm
 have hu: ((S:ℝ)*Q)^k ≤ Real.exp ((k:ℝ)*(P (L B)+V)):=by rw [Real.exp_nat_mul, Real.exp_add]; exact pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) huQ) (mul_le_mul hq v.2 huQ (Real.exp_pos _).le) _
 refine hv.trans_le ((mul_le_mul he' hu (by positivity : (0:ℝ) ≤ ((S:ℝ)*Q)^k) (Real.exp_pos _).le).trans ?_); rw [←Real.exp_add]; apply Real.exp_monotone
 change _≤ X/Y/4; unfold P V; change (X/Y/64+Y/10000)+(k:ℝ)*(Y/100/64+Y/10000)≤ X/Y/4; change Y/100≤ X/Y at hp; linarith only [hp,hk,div_nonneg h1 hY.le]
end YM.CF.Roots

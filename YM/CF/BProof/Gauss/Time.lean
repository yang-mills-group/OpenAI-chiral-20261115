import YM.CF.BProof.Gauss.Beam
import YM.CF.BProof.PL

/-! PL powers for the horizon used in the finite spectral expansion. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Gauss.Bin
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Roll Precision RealM SignScalar
open scoped Topology BigOperators Classical Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
variable (p : ℝ→ℝ) (hp:PL p) (h:∀ y,1≤p y) {a:ℝ}(ha:0<a)(hk:a≤1)

-- frequently used PL sqrt/inverse. could weaken to pay⁻¹ bounds.
include h
lemma pay_hi (y:ℝ):pay (p y)≤1:=by
 have hi : 1≤Real.sqrt (p y):= (by have hi:=Real.sqrt_le_sqrt (h y); simpa using hi); exact inv_le_one_of_one_le₀ hi
include hp
lemma pay_route : PL (fun y=> pay (p y)):=by
 apply PL.by_le (PL.const 1); filter_upwards with y; change |pay (p y)| ≤ |(1:ℝ)| -- syntax
 have hz:0≤pay (p y):=by unfold pay; positivity
 rw [abs_of_nonneg hz, abs_of_nonneg zero_le_one]; exact pay_hi p h y
lemma pay_bill : PL (fun y=>(pay (p y))⁻¹):=by
 refine PL.by_le hp ?_; filter_upwards with y; unfold pay
 have ht := one_pos.trans_le (h y); rw [inv_inv,abs_of_nonneg ht.le,abs_of_nonneg (Real.sqrt_nonneg _)]; nlinarith [Real.sq_sqrt ht.le,h y]

def stride (r y:ℝ→ℝ) (k z:ℝ) := ⌈k *(r z / y z) * Real.log z⌉₊ -- generic buys p/a.
omit hp h
lemma stride_pl {r a:ℝ→ℝ}(h:PL r)(v:PL (fun y=>(a y)⁻¹))(hr:∀ᶠ x:ℝ in atTop,0<r x)(ha:∀ᶠ x:ℝ in atTop,0<a x)(k:ℝ)(p:0≤k) : PL (fun y=>(stride r a k y:ℝ)):=by
 apply PL.ceil; simp only [div_eq_mul_inv]; exact ((PL.const k).mul (h.mul v)).mul PL.log_y
 filter_upwards [ha,hr,eventually_ge_atTop (1:ℝ)] with y h k' he; have hh:=Real.log_nonneg he; positivity
lemma stay {p a y:ℝ} (hp:0<p)(h:a≤p)(ha:0<a)(hy:1<y)(k:ℝ)(v:0<k)(n:ℕ)(hv:k*(p/a)*Real.log y ≤ n):
    (1-p⁻¹*a)^n ≤ coin y (-k) 0 0:=by
 have h': p⁻¹*a≤1:= by rw [inv_mul_le_iff₀ hp, mul_one]; exact h
 apply le_trans (pow_le_pow_left₀ (by linarith : 0≤1-p⁻¹*a) (le_trans (by ring_nf; exact le_rfl : 1-p⁻¹*a≤ -(p⁻¹*a)+1) (Real.add_one_le_exp (- (p⁻¹*a)))) n)
 rw [←Real.exp_nat_mul]; apply Real.exp_monotone; rw [mul_zero,mul_zero,add_zero,add_zero]; calc
   _ ≤ k*(p/a)*Real.log y*(-(p⁻¹*a)):= mul_le_mul_of_nonpos_right hv (by have hv:0≤ p⁻¹*a := mul_nonneg (by positivity) ha.le; linarith)
   _ = _:=by field_simp

include hp h ha hk
lemma buys : let n:=stride p (fun _=>a) 6; PL (fun y=>(n y:ℝ)) ∧ ∀ᶠ y:ℝ in atTop, Qualified (p y) a (n y) ∧ scope (p y) a (n y)≤ y⁻¹^2:=by
 intro n; have h':=fun x=> one_pos.trans_le (h x); refine ⟨stride_pl hp (PL.const _) (Eventually.of_forall h') (Eventually.of_forall fun _=>ha) _ (by norm_num),?_⟩
 let P (y:ℝ):=pay (p y)* p y/a; have hM:1≤ maximum a:=max_ge (p:=1) le_rfl ha hk
 have hP:PL P:=by unfold P; simp only [div_eq_mul_inv]; exact ((pay_route p hp h).mul hp).mul (PL.const _)
 let R(y:ℝ):=p y*P y*(2*maximum a)
 have hv: PL R:= (hp.mul hP).mul (PL.const _)
 filter_upwards [eventually_gt_atTop (1:ℝ),coin_strongLt (a:=1) (b:=0) (by norm_num) hP,coin_strongLt (a:=1) (b:=0) (by norm_num) hv] with y hy H1 H2
 set m:= n y
 have hz:0<y:= one_pos.trans hy; rw [coinY hz] at H1 H2
 have hh:6*((p y)/a)*Real.log y≤m:= Nat.le_ceil _; have h3:=h' y; have he:0<m:=by
    have hr:=Real.log_pos hy; exact Nat.cast_pos.mp (lt_of_lt_of_le (by positivity : (0:ℝ)<6*((p y)/a)*Real.log y) hh)
 let z:=tail (p y) a m; have ht: z≤P y* coin y (-6) 0 0:= by
   have ht := stay h3 (hk.trans (h y)) ha hy 6 (by norm_num) m hh; change afford (p y) a ^m≤coin y (-6) 0 0 at ht
   unfold z tail; have v:(1-afford (p y) a)⁻¹ =p y /a:=by unfold afford; rw [sub_sub_cancel]; field_simp -- tune
   rw [v]; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht (by positivity)) (by unfold pay; positivity)); unfold P; exact le_of_eq (by ring)
 have hx: y*(coin y (-6) 0 0) ≤ y⁻¹^2:=by
    rw [show coin y (-6) 0 0=y⁻¹^6 from Eq.symm (by nth_rw 1 [←coinY hz]; rw [coin_inv,coin_pow]; ring_nf)]; field_simp; nlinarith only [one_lt_pow₀ hy (show (3:ℕ)≠0 by norm_num)] -- tune
 have e:0 ≤ coin y (-6) 0 0:= (coin_pos ..).le
 refine ⟨⟨h _,hk,ha,he, (ht.trans ((mul_le_mul_of_nonneg_right ((le_abs_self (P y)).trans H1.le) e).trans hx)).trans ?_⟩,?_⟩
 · field_simp; nlinarith
 apply le_trans (b:=(p y)*(P y*coin y (-6) 0 0*(2*maximum a))) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht (by positivity)) h3.le); rw [show (p y)*(P y*coin y (-6) 0 0*(2*maximum a)) = R y*coin y (-6) 0 0 from ?_]; swap -- tune meta pattern
 · unfold R; ring
 exact (mul_le_mul_of_nonneg_right ((le_abs_self _).trans H2.le) e).trans hx
end YM.CF.BProof.Gauss.Bin

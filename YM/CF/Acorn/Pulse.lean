import YM.CF.Acorn.Cedar
/-! Transfer weight series. Exact finite terms, exponential in a component, not in volume. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Acorn
open Function Filter Finset
open scoped Topology BigOperators
variable {f:ℕ→ℝ} {K a:ℝ}
def pairs (k:ℕ): Finset (ℕ × ℕ):= (Finset.antidiagonal k).filter fun i=>i.1≤2
def plume (K:ℝ) (a:ℝ):ℕ→ℝ
| 0=>a
| i+1=> (∑ p ∈ (pairs i).attach, K*plume K a p.val.2)/(i+1:ℝ)
termination_by n=>n
decreasing_by obtain h:= Finset.mem_antidiagonal.mp (Finset.mem_filter.mp p.property|>.1); omega
lemma p_eq (i) : plume K a (i+1) = (∑ p∈ pairs i,K*plume K a p.2)/(i+1:ℝ):=by rw [plume]; congr 1; rw [← sum_attach (pairs i)]
lemma p_pol (h:0≤K)(g:0≤a)(i):0≤plume K a i:=by
 induction i using Nat.strong_induction_on with
 | h i ih=>
   cases i with
   | zero=>rw [plume]; exact g
   | succ i=>
     rw [p_eq]; refine div_nonneg (sum_nonneg (fun j t=>mul_nonneg h (ih j.2 ?_))) (by positivity); have he:= mem_antidiagonal.mp (mem_filter.mp t|>.1); omega
lemma out_proc (n:ℕ)(h:0≤K)(g:0≤a) : ∑ i∈range (n+1), plume K a i ≤ Real.exp (3*K)*a:=by
 cases n with
 | zero=>simp only [Nat.zero_add, range_one, sum_singleton,plume]; exact le_mul_of_one_le_left g (Real.one_le_exp (by positivity))
 | succ N =>
 let f:= plume K a; have he:=p_pol h g
 let T:ℝ→ℝ:=fun t=> ∑ i∈range (N+2), f i*t^i
 let P (i:ℕ)(x:ℝ):ℝ:= ∑ k∈pairs i, K*f k.2*x^i
 let s (x:ℝ):=∑ i∈range (N+1), P i x
 have ht (x):HasDerivAt T (s x) x:=by
   have hx:T=fun x=>f 0+∑ i∈range (N+1),f (i+1)*x^(i+1):=by funext x; unfold T; rw [Finset.sum_range_succ',pow_zero,mul_one,add_comm]
   rw [hx,show s x = 0 + ∑ i∈range (N+1),P i x by unfold s; rw [zero_add]]; refine (hasDerivAt_const _ _).add (HasDerivAt.fun_sum (fun i (_:i∈range (N+1))=>?_));
   have H : P i x=f (i+1)*((i+1:ℝ)*x^i):=by unfold P f; rw [←sum_mul,p_eq]; field_simp
   rw [H]; simpa using ((hasDerivAt_pow (i+1) x).const_mul (f (i+1)))
 have hz (x:ℝ)(hx:x∈ Set.Icc 0 1): s x ≤ 3*K * T x:=by
    have hp:0≤x:=hx.1; let p(z:ℕ×ℕ):=K*f z.2*x^(z.1+z.2)
    calc
     _ = ∑ i∈ range (N+1),∑ z∈ pairs i,p z:=by refine sum_congr rfl fun i _=> Eq.symm ?_; refine sum_congr rfl fun v hv=>?_ ; unfold p; rw [mem_antidiagonal.mp (mem_filter.mp hv).1]
     _ ≤ ∑ z∈ range 3 ×ˢ range (N+2),p z:=by
       rw [← sum_biUnion]
       · refine sum_le_sum_of_subset_of_nonneg ?_ (fun i H _=> mul_nonneg (mul_nonneg h (he _)) (pow_nonneg hp _)); intro i h; obtain ⟨j,t,q⟩:= mem_biUnion.mp h; obtain ⟨a,l⟩:=mem_filter.mp q; replace a:=mem_antidiagonal.mp a; rw [mem_range] at t; rw [mem_product]; simp only [mem_range]; omega
       intro i j k l u; exact disjoint_left.mpr fun z w t=> u ((mem_antidiagonal.mp (mem_filter.mp w).1).symm.trans (mem_antidiagonal.mp (mem_filter.mp t).1))
     _ ≤ ∑ z∈ range 3 ×ˢ range (N+2), K*(f z.2*x^z.2):=by
       refine sum_le_sum fun i _=> ?_; unfold p; rw [pow_add,mul_assoc,mul_comm (x^_),mul_comm (x^i.2)] -- tune
       have he' : x^i.1≤1:=pow_le_one₀ hp hx.2
       exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right he' (pow_nonneg hp i.2)).trans (one_mul _|>.le)) (he _)) h
     _ = _:=by unfold T; rw [Finset.sum_product]; simp [←Finset.mul_sum, mul_assoc]
 let Q(t:ℝ):= Real.exp (- (3*K*t))*T t; let V:=Set.Icc (0:ℝ) 1
 have hq(t):HasDerivAt Q (Real.exp (- (3*K*t))* (s t-3*K*T t)) t:=by
   have he:= (((hasDerivAt_id' t).const_mul (3*K)).neg.exp).mul (ht t); convert! he using 1; simp only [Pi.neg_apply]; ring
 have hv: Q 1 ≤ Q 0:= (antitoneOn_of_deriv_nonpos (convex_Icc _ _) ((show Continuous Q from continuous_iff_continuousAt.mpr fun i=> (hq i).continuousAt).continuousOn) (fun x _=>(hq x).differentiableAt.differentiableWithinAt) (fun x hx=>by rw [(hq _).deriv]; exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr (hz _ (interior_subset hx))))) ⟨le_rfl,zero_le_one⟩ ⟨zero_le_one,le_rfl⟩ zero_le_one
 unfold Q T at hv
 simp only [mul_one, mul_zero, neg_zero,Real.exp_zero,one_mul, Real.exp_neg,one_pow] at hv
 rwa [sum_eq_single (f:=fun i=>f i*0^i) 0 (by intro j _ h; simp [h]) (by simp),pow_zero,mul_one,show f 0=a by unfold f; rw [plume],inv_mul_le_iff₀ (by positivity)] at hv
end YM.CF.Acorn

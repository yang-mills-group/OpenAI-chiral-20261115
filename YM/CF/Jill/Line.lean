import YM.CF.Ember.Pool
import YM.CF.Ember.Rum
import Mathlib.LinearAlgebra.Lagrange
set_option autoImplicit false
noncomputable section
namespace YM.CF.Jill
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
variable {ι E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]{A:Tax ι}{f:ι→ℂ→E}{d:ℤ}
-- polynomial scales via DSlope repeated
private lemma shift(f:ℂ→ E)(z:ℂ): f z=f 0+z • dslope f 0 z:=by
 by_cases h:z=0; · simp [h];
 rw [dslope_of_ne _ h,slope_def_module,sub_zero,smul_smul,mul_inv_cancel₀ h,one_smul,add_comm,sub_add_cancel]
lemma polynomial (h:Act A d f)(k:ℕ):∃ (Y:ι→ℕ→E)(u:ι→ℂ→E), Act A d u ∧∀ i z, f i z=(∑ j∈range k, z^j • Y i j)+ z^k • u i z :=by
 induction k generalizing f with
 | zero=>exact ⟨fun _ _=>0,f,h,by simp⟩
 | succ k ih=> obtain ⟨Y,V,hv,p⟩:= ih h; let X(i:ι)(j:ℕ):E:= if j=k then V i 0 else Y i j; refine ⟨X, _,hv.lip,fun i z=>?_⟩; rw [p i z,sum_range_succ, sum_congr rfl (g:=fun j=> z^j • X i j) (fun j (hj:j∈range k)=>by rw [show X i j= _ from if_neg (Nat.ne_of_lt (mem_range.mp hj))]), shift (V i) z, smul_add,pow_succ,← smul_smul, show X i k=_ from if_pos rfl,add_assoc]
-- interpolation moments Lagrange
open Polynomial
def bead(k:ℕ)(u:ℝ)(l:ℕ):ℝ:=Polynomial.eval u (Lagrange.basis (range k) (fun i:ℕ=>(i:ℝ)) l)
lemma bead_p(k n:ℕ)(h:n<k)(x:ℝ): ∑ j∈range k,bead k x j*(j:ℝ)^n=x^n:=by
 let v(j:ℕ):= (j:ℝ); let P: Polynomial ℝ:=X^n
 have ht:Set.InjOn v (range k):= (show Function.Injective v from Nat.cast_injective).injOn; have he:=congrArg (Polynomial.eval x) (Lagrange.eq_interpolate (f:=P) ht (by simp [P,h])); simp [Lagrange.interpolate_apply, Polynomial.eval_finsetSum,P,mul_comm] at he -- tune
 simpa [bead,v,mul_comm] using he.symm
lemma bead_one(k)(h:0<k)(x:ℝ): ∑ j∈range k,bead k x j=1:=by simpa using bead_p _ _ h x
lemma bead_bound(k:ℕ):∃ C:ℝ,0<C∧∀ x:ℝ,|x|≤1→∑ j∈range k,|bead k x j|≤C:=by
 let U(x:ℝ):= ∑ j∈range k,|bead k x j|
 have h:Continuous U:=by unfold U; apply continuous_finsetSum; intro i _; exact (Polynomial.continuous ..).abs
 obtain ⟨C,Q⟩:= (isCompact_Icc (α:=ℝ) (a:=-1) (b:=1)).bddAbove_image h.continuousOn
 exact ⟨max C 1,lt_max_of_lt_right one_pos,fun i p=> le_trans (Q ⟨i, abs_le.mp p,rfl⟩) (le_max_left ..)⟩
-- scaling identity
lemma line_g(k l:ℕ)(h:l<k)(x:ℝ)(u:ℂ)(w:E): ∑ j∈range k,(bead k x j:ℂ) • (((j:ℂ)*u)^l • w)= ((x:ℂ)*u)^l • w:=by
 simp only [smul_smul]; rw [← Finset.sum_smul]; congr 1; simp_rw [mul_pow,← mul_assoc, ←Complex.ofReal_natCast,← Complex.ofReal_pow,← Complex.ofReal_mul, ← sum_mul, ← Complex.ofReal_sum]; -- inspect
 simp [bead_p k l h x] -- tune
lemma plunge (h:Act A d f)(k:ℕ)(c:0<k):∃ a C:ℝ,0<a ∧ 0<C ∧ ∀ i (x:ℝ),|x|≤1→∀ u:ℂ,‖u‖<a → ‖f i ((x:ℂ)*u)-∑ j∈range k,(bead k x j:ℂ) • f i ((j:ℂ)*u)‖≤ C*(A.r i)^d*‖u‖^k:=by
 obtain ⟨Y,V,⟨a,T,ha,ht,H⟩,p⟩:= polynomial h k; obtain ⟨b,hb,B⟩:=bead_bound k
 have hk : 0<(k:ℝ):=by exact_mod_cast c
 refine ⟨a/(k:ℝ),T+b*((k:ℝ)^k*T),by positivity,by positivity,fun i x hx u hu=>?_⟩
 simp_rw [p,smul_add,Finset.smul_sum,sum_add_distrib]; conv => lhs; rw [sum_comm (s:=range k) (t:=range k),sum_congr rfl (fun j hj=>line_g _ _ (mem_range.mp hj) ..),add_sub_add_left_eq_sub]
 let K:ℝ:=k; let m:=A.r i
 have he:0<m:=A.pos i; have hp:= (_root_.lt_div_iff₀ hk).mp hu; have hz:‖(x:ℂ)*u‖≤ ‖u‖:=(le_trans (le_of_eq (norm_mul ..)) (mul_le_of_le_one_left (norm_nonneg _) (by simpa using hx))); have hxu: ‖u‖<a:= hu.trans_le (div_le_self ha.le (by exact_mod_cast c))
 let g(l:ℕ):=(bead k x l:ℂ) • (((l:ℂ)*u)^k • V i ((l:ℂ)*u))
 have hy:‖∑ l∈range k,g l‖ ≤ b*(K^k*‖u‖^k*(T*m^d)):=calc
   _ ≤ ∑ l∈range k, ‖g l‖:= norm_sum_le ..
   _ ≤ ∑ l∈range k, |bead k x l| *(K^k*‖u‖^k*(T*m^d)):=by
     refine sum_le_sum fun j hj=>?_; have hx:‖(j:ℂ)*u‖≤ K*‖u‖:=by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (by unfold K; simp; exact_mod_cast (mem_range.mp hj).le) (norm_nonneg _)
     have hg: ‖(j:ℂ)*u‖<a:=hx.trans_lt (by change (k:ℝ)*_<_; linarith)
     unfold g; rw [norm_smul,norm_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs, ← mul_pow]; exact mul_le_mul_of_nonneg_left (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx k) (H i _ hg).2 (norm_nonneg _) (pow_nonneg (mul_nonneg hk.le (by positivity)) _)) (abs_nonneg _)
   _ ≤ _:=by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (B _ hx) (by unfold K; positivity)
 refine (norm_sub_le ..).trans ((add_le_add (show _ ≤ ‖u‖^k*(T*m^d) from ?_) hy).trans (le_of_eq ?_))
 rw [norm_smul,norm_pow]; exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hz k) (H i _ (hz.trans_lt hxu)).2 (norm_nonneg _) (by positivity)
 all_goals unfold K m; ring
end YM.CF.Jill

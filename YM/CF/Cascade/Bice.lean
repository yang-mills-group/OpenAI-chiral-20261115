import YM.CF.Cascade.Rudder
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cascade
open Function Filter Metric Finset Lattice Wilson Next.Free Bloch Laurent Scroll Precision Exterior Lat Ember Aroma
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker
variable {j t:ℕ}{n c f:Side}{k a b:ℝ}
open Tree SU Font Cube Extra.Iteration Nacre
open Thera Fock Dial Peaks Tulip Paige NormedSpace
open Spire Vault Laic Kennel Rush Fir Branch Tenant
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
lemma sugar :∃ C:ℝ,0≤C∧∃ j:ℕ,∀ (N:Side),j ≤ N.val →Even N.val→ ∑ i:Site N,(‖bark i‖^3)⁻¹≤ C*(N.val:ℝ)^4:=by
 have he: SnowH (fun _=>0) 0:=⟨fun _ _=> contDiffAt_const,fun t p x=>by simp,fun {μ} h e=>by simp⟩
 obtain ⟨D,H⟩:= frosted he (A:=1) (B:=1) (e:=1) le_rfl zero_le_one zero_le_one
 obtain ⟨N,h⟩:= neck (a:=1/8) (by norm_num); refine ⟨|D|,abs_nonneg _,N,fun n g p=>?_⟩
 have hx := h n g; have ht:8*1*Ember.pinch n ≤1:=by linarith
 let f(k:Site n):=(‖bark k‖^3)⁻¹; have hs:MapH (fun _=>0) 1 1 1 f:=by
   constructor; intro k hk; unfold f; rw [norm_inv,norm_pow, Real.norm_of_nonneg (norm_nonneg _),one_div]; have hh:= pinch_pos n
   apply inv_anti₀ (pow_pos hh _); exact (pow_le_pow_of_le_one hh.le (by linarith) (by norm_num)).trans (pow_le_pow_left₀ hh.le (Ember.torch _) _)
   intro k hk; unfold f; rw [sub_zero,norm_inv,norm_pow,Real.norm_of_nonneg (norm_nonneg _),one_mul]; apply le_add_of_nonneg_right; exact div_nonneg (pinch_pos _|>.le) (by positivity)
 have hy:= H f p ht hs; rw [zero_mul,sub_zero,Real.norm_eq_abs] at hy; apply (div_le_iff₀ (pow_pos (side_pos n) 4)).mp; exact (le_abs_self _).trans (hy.trans (le_abs_self _)) -- direction
lemma chillY (j:ℕ)(p:1≤j):∃ C:ℝ, 0<C∧∀ (M:Male)(N:Side)(i:Site N), ‖(shell j M.val (mel i))⁻¹‖ ≤ C*(‖bark i‖^2)⁻¹:=by
 let I:= Σ (_:Male), Σ N: Side, Site N; let M(i:I):=i.1.val; let X(i:I):= bark i.2.2; let t:Ember.Tax I:=⟨fun i=> ‖X i‖,2*Real.pi,fun i=>(pinch_pos _).trans_le (Ember.torch _),fun i=> mem_closedBall_zero_iff.mp (Stationary.earth_bounded _ (bark_inside _))⟩
 obtain ⟨C,hc,H⟩:= Move.chill_mag (p:=fun i (_:ℂ)=> river (X i)) (t:=t) M (fun i=> i.1.property) j p X (fun i=>rfl) (fun i=>rfl) (fun i=>bark_inside _)
 refine ⟨C⁻¹,inv_pos.mpr hc,fun m N i=>?_⟩; let J:I:=⟨m,N,i⟩; have ht:= H J; change C*‖bark i‖^(2:ℤ)≤ ‖shell j m.val (river (bark i))‖ at ht; rw [show river (bark i)=mel i from riverB _, zpow_ofNat] at ht; rw [norm_inv, ← mul_inv]; exact inv_anti₀ (mul_pos hc (pow_pos (t.pos J) _)) ht
section tr
variable {X:Type*}[Fintype X][DecidableEq X]
def kg(A:Op X):ℝ:= (Matrix.trace (star A *A)).re
lemma kg_I(A:Op X):kg A=∑ i,‖acts A (basisKet i)‖^2:=by
 unfold kg Matrix.trace; rw [Complex.re_sum]; refine sum_congr rfl fun i _=> ?_; rw [← inner_self_eq_norm_sq (𝕜:=ℂ),show inner ℂ (acts A (basisKet i)) (acts A (basisKet i))= inner ℂ (basisKet i) (acts (star A*A) (basisKet i)) from ?_,basis_inner,basis_act]; rfl
 nth_rw 1 [← star_star A]; exact (act_inner ..).trans (by rw [act_mul]) -- tune spin coerc
lemma traceK(A:Op X):kg A=∑ i: X,∑ j:X, ‖A j i‖^2:=by
 unfold kg; simp_rw [Matrix.trace, Complex.re_sum, Matrix.diag_apply, Matrix.mul_apply,Complex.re_sum]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; change (star _ * _:ℂ).re= _; rw [mul_comm]; exact inner_self_eq_norm_sq (𝕜:=ℂ) (x:=A j i) -- tune
lemma kgN(A: Op X): 0 ≤ kg A:=by rw [kg_I]; exact sum_nonneg fun _ _=> sq_nonneg _
lemma kgt(A:Op X): kg (star A)=kg A:=by unfold kg; rw [star_star,Matrix.trace_mul_comm]
lemma kgs(A B:Op X):kg (A+B) ≤ 2*(kg A+kg B):=by
 rw [kg_I,kg_I,kg_I,←sum_add_distrib,mul_sum]; apply sum_le_sum; intro i _; rw [act_add]; apply (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le ..) 2).trans; nlinarith only [sq_nonneg (‖acts A (basisKet i)‖-‖acts B (basisKet i)‖)]
lemma kg_a(A B:Op X):kg (A*B)≤ ‖A‖^2*kg B:=by
 rw [kg_I,kg_I,mul_sum]; apply sum_le_sum; intro i _; rw [act_mul,←mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) ((acts A).le_opNorm _) _
lemma kg_b(A B:Op X):kg (A*B)≤ kg A*‖B‖^2:=by
 rw [← kgt,star_mul,mul_comm]; exact (kg_a (star B) (star A)).trans_eq (by rw [norm_star,kgt])
lemma kg_c(A:Op X):|A.trace.re| ≤ Fintype.card X +kg A:=by
 rw [traceK, Matrix.trace,Complex.re_sum,show (↑(Fintype.card X):ℝ)=∑ _: X,(1:ℝ) by simp,←sum_add_distrib]; apply (abs_sum_le_sum_abs ..).trans; apply sum_le_sum; intro i _; refine (Complex.abs_re_le_norm (A i i)).trans (le_trans ?_ (add_le_add_right (single_le_sum (f:=fun j : X=> ‖A j i‖^2) (fun i _=> sq_nonneg _) (mem_univ i)) 1)); nlinarith [norm_nonneg (A i i)] -- tune
lemma kg_d(A:Op X): |(A*A).trace.re|≤kg A:=by
 rw [traceK,Matrix.trace,Complex.re_sum]; apply (abs_sum_le_sum_abs ..).trans
 let f(i j:X):ℝ:=(‖A i j‖^2+‖A j i‖^2)/2; calc
    _ ≤ ∑ i:X,∑ j:X,f i j:=by apply sum_le_sum; intro i _; change |((A*A) i i).re|≤ _; rw [Matrix.mul_apply,Complex.re_sum]; apply (abs_sum_le_sum_abs ..).trans; refine sum_le_sum fun j _=> (Complex.abs_re_le_norm _).trans ?_; unfold f; rw [norm_mul]; nlinarith only [sq_nonneg (‖A i j‖-‖A j i‖)]
    _ = _:=by unfold f; simp_rw [← sum_div,sum_add_distrib]; rw [sum_comm]; ring_nf -- tune
end tr
end YM.CF.Cascade

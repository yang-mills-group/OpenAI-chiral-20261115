import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Trace
/-! finite period angular diagonalization. Always real Lie chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Weave
open Function Filter Finset
open scoped Topology BigOperators Classical InnerProductSpace
variable {E I:Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E][Fintype I]
local notation "EndE" => E →L[ℝ] E
def Flare (A:E→L[ℝ] E)(x:E)(l:ℝ):Prop:= A x=l • x
def Harp (b:OrthonormalBasis I ℝ E)(A:E→L[ℝ] E)(f:I→ℝ) : Prop:= ∀ i, Flare A (b i) (f i)
def Margins (A:E→L[ℝ] E)(p q:ℝ):Prop:= ∀ x, inner ℝ x (A x)∈ Set.Icc (p*‖x‖^2) (q*‖x‖^2)
lemma Margins.broad {A:E→L[ℝ] E}{a b c d:ℝ}(h:Margins A b c)(p:a ≤ b)(q:c≤ d): Margins A a d:=fun x=>⟨(mul_le_mul_of_nonneg_right p (sq_nonneg _)).trans (h x).1,(h x).2.trans (mul_le_mul_of_nonneg_right q (sq_nonneg _))⟩
lemma basis_harp (A:E→L[ℝ] E)(h:IsSelfAdjoint A) : ∃ (I:OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E) (v:Fin _→ℝ), Harp I A v:=by -- complete?
 let q:= ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp h; refine ⟨ q.eigenvectorBasis rfl, q.eigenvalues rfl, ?_⟩; intro i; exact q.apply_eigenvectorBasis rfl i
namespace Flare
variable {A B : E →L[ℝ] E} {v:E} {c d q :ℝ}
lemma one : Flare 1 v 1:= by unfold Flare; simp
lemma zero : Flare 0 v 0:= by unfold Flare; simp
lemma scale (h:Flare A v c) (q:ℝ): Flare (q • A) v (q*c):=by rw [Flare]; rw [ContinuousLinearMap.smul_apply, show A v=_ from h, smul_smul]
lemma mul (h:Flare A v c)(g:Flare B v d): Flare (A*B) v (c*d):=by unfold Flare; rw [ContinuousLinearMap.mul_apply,show B v=_ from g,map_smul,show A v=_ from h,smul_smul,mul_comm c d]
lemma plus (h:Flare A v c)(g:Flare B v d):Flare (A+B) v (c+d):=by unfold Flare at *; simp [h,g,add_smul]
lemma sub (h:Flare A v c)(g:Flare B v d):Flare (A-B) v (c-d):=by unfold Flare at *; simp [h,g,sub_smul]
lemma pow (h:Flare A v c)(n:ℕ): Flare (A^n) v (c^n):=by induction n with|zero=> simpa only [pow_zero] using (one (v:=v))|succ n ih=> rw [pow_succ,pow_succ]; exact ih.mul h
lemma rays {N:Type*}(S:Finset N)(A:N→ E→L[ℝ] E)(c:N→ℝ)(p:∀ i∈S,Flare (A i) v (c i)): Flare (∑ i∈S,A i) v (∑ i∈S,c i):=by unfold Flare; rw [ContinuousLinearMap.sum_apply,sum_smul]; exact sum_congr rfl p
end Flare
variable {b: OrthonormalBasis I ℝ E}{A B: E→L[ℝ] E}{f g:I→ℝ}{p q:ℝ}
namespace Harp
lemma upper (h:Harp b A f)(x y:E): inner ℝ y (A x)= ∑ i, f i * (inner ℝ (b i) x * inner ℝ (b i) y):=by
 conv_lhs=> rhs; arg 2; rw [← b.sum_repr' x] -- tune
 rw [map_sum,inner_sum]; apply sum_congr rfl; intro i u; rw [map_smul, real_inner_smul_right, show A (b i)=_ from h i,real_inner_smul_right, real_inner_comm (b i) y]; ring
lemma self (h:Harp b A f): IsSelfAdjoint A:=by
 rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]; intro x y; change inner ℝ _ _=_; rw [real_inner_comm y]; change inner ℝ y (A x)=inner ℝ x (A y) -- tune
 rw [h.upper,h.upper]; exact sum_congr rfl fun i _=>by rw [mul_comm (inner _ _ x)]
lemma margin (h:Harp b A f) : Margins A p q ↔ ∀ i, f i∈ Set.Icc p q:= by
 constructor
 · intro e i; have t:= e (b i); rw [show A (b i)=_ from h i,real_inner_smul_right, real_inner_self_eq_norm_sq, b.orthonormal.1] at t; simpa using t
 intro g x; rw [h.upper,←b.sum_sq_norm_inner_right x]; simp_rw [Real.norm_eq_abs,sq_abs, mul_sum, ←pow_two]; exact ⟨sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right (g i).1 (sq_nonneg _)),sum_le_sum fun i _=>mul_le_mul_of_nonneg_right (g i).2 (sq_nonneg _)⟩
-- Point evaluations via self adjoint
lemma wrist (h:Harp b A f)(x:E)(i:I): inner ℝ (b i) (A x)= f i * inner ℝ (b i) x:=by
 apply Eq.trans (b:=inner ℝ (A (b i)) x); exact ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp h.self) (b i) x).symm; rw [show A (b i)=_ from h i,real_inner_smul_left]
lemma cap (h:Harp b A f)(v:0≤p)(g:∀ i, |f i|≤ p): ‖A‖≤ p:=by
 apply ContinuousLinearMap.opNorm_le_bound _ v; intro x; apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg v (norm_nonneg _))).mp; rw [←b.sum_sq_norm_inner_right (A x), mul_pow,←b.sum_sq_norm_inner_right x,mul_sum]; refine sum_le_sum fun i _=>?_ ; rw [h.wrist,norm_mul,mul_pow]; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (g i) _) (sq_nonneg _)
variable [DecidableEq I]
lemma toM (h:Harp b A f): LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap= Matrix.diagonal f:=by ext i j; rw [LinearMap.toMatrix_apply]; simp_rw [OrthonormalBasis.coe_toBasis_repr_apply,OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe,show A (b j)=_ from h j,map_smul]; by_cases h:i=j <;> simp [h, Matrix.diagonal_apply, PiLp.smul_apply] -- tune
lemma det (h:Harp b A f) : LinearMap.det A.toLinearMap= ∏ i,f i:=by rw [← LinearMap.det_toMatrix b.toBasis, h.toM, Matrix.det_diagonal]
lemma trace (h:Harp b A f) : LinearMap.trace ℝ E A.toLinearMap= ∑ i,f i:=by rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis, h.toM, Matrix.trace_diagonal] -- tune
end Harp
lemma Margins.cap (h:Margins A (-p) p)(v:0≤ p)(q:IsSelfAdjoint A) : ‖A‖≤ p:=by obtain ⟨I,f,g⟩:= basis_harp A q; apply g.cap v; intro i; exact abs_le.mpr ((g.margin.mp h) i)
-- polarization bound follows from inner le if self? need margins iff cap (actually cap→ margins via Cauchy)
lemma Margins.budget (h:‖A‖≤ p) : Margins A (-p) p:=by
 intro i; have t: |inner ℝ i (A i)|≤p*‖i‖^2:= (abs_real_inner_le_norm ..).trans ((mul_le_mul_of_nonneg_left ((A.le_opNorm i).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))) (norm_nonneg _)).trans_eq (by ring)); rw [neg_mul]; exact abs_le.mp t
end YM.CF.BPress.Weave

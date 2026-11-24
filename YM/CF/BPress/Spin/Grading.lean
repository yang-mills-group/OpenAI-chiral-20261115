import YM.CF.BPress.Spin.Trans
/- Price tools for PSD inequalities on full finite spaces (complex L2, real scalars). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Spin
open Function Fock Filter NormedSpace Finset
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
attribute [local instance] opCStarAlgebra
namespace Quad
variable {I:Type*}[Fintype I][DecidableEq I]{P Q:Op I}{a b:ℝ}
def energy (P:Op I)(v:Ket I):=(inner ℂ v (acts P v)).re
lemma e_pow(A:Op I)(v:Ket I): energy (star A*A) v=‖acts A v‖^2:=by unfold energy; rw [act_mul, ←act_inner,star_star]; exact inner_self_eq_norm_sq (𝕜:=ℂ) (acts A v)
@[simp] lemma e_one (v:Ket I):energy 1 v=‖v‖^2:= by unfold energy; rw [act_one]; exact inner_self_eq_norm_sq (𝕜:=ℂ) v
lemma e_twist (U:UNI I)(P:Op I)(v:Ket I):energy (twist U P) (acts U.val v)=energy P v:=by unfold energy; rw [twist_formula,act_mul,act_mul,act_unit,act_unit_inner]
lemma e_sub(P Q:Op I)(v:Ket I):energy (P-Q) v=energy P v-energy Q v:=by unfold energy; rw [act_sub,inner_sub_right]; rfl
lemma e_add(P Q:Op I)(v:Ket I):energy (P+Q) v=energy P v+energy Q v:=by unfold energy; rw [act_add,inner_add_right]; rfl
lemma e_scale(a:ℝ)(P:Op I)(v:Ket I): energy (a • P) v=a*energy P v:=by unfold energy; rw [show a • P=(a:ℂ) • P from Eq.symm (by ext; simp [Complex.real_smul]),act_smul,inner_smul_right]; simp
lemma e_nonneg (p:0≤P)(v:Ket I):0≤ energy P v:=by obtain ⟨P,rfl⟩:= CStarAlgebra.nonneg_iff_eq_star_mul_self.mp p; rw [e_pow]; exact sq_nonneg _
lemma e_rec (p:IsSelfAdjoint P)(u:∀ v,0≤energy P v): 0 ≤ P:=by
 obtain ⟨U,A,h⟩:= spectral_exists P p; rw [h,←spectral_zero U,spectral_le]; intro i
 have ht:= u (acts U.val (basisKet i)); rw [h,spectral,e_twist,energy,basis_inner,basis_act] at ht; simpa using ht -- tune reduction
lemma e_mono (p:P≤Q)(x:Ket I) : energy P x ≤energy Q x:=by
 have he:=e_nonneg (sub_nonneg.mpr p) x; rw [e_sub] at he; linarith
lemma e_le (h:IsSelfAdjoint P)(p:IsSelfAdjoint Q)(u:∀ v,energy P v≤energy Q v): P≤Q:= sub_nonneg.mp (e_rec (p.sub h) fun v=>by rw [e_sub]; exact sub_nonneg.mpr (u v))
lemma e_sand (Q P:Op I)(v:Ket I): energy (star P*Q* P) v=energy Q (acts P v):=by unfold energy; rw [act_mul,act_mul,←act_inner,star_star]
lemma e_s (p:IsSelfAdjoint P) (Q:Op I)(v:Ket I): energy (P*Q*P) v=energy Q (acts P v):= by have he:= e_sand Q P v; rwa [p] at he -- tune
lemma e_proj (h:IsStarProjection P)(v:Ket I): energy P v=‖acts P v‖^2:= by have he := e_pow P v; rwa [h.isSelfAdjoint,h.isIdempotentElem.eq] at he
lemma s_mono (u:IsSelfAdjoint P){A B:Op I}(p:A≤ B): P*A*P≤ P*B*P:=by simpa only [u.star_eq] using star_right_conjugate_le_conjugate p P
lemma kron_one (p:P ≤ Q)(J:Type*)[Fintype J][DecidableEq J]: P⊗ₖ(1:Op J)≤Q⊗ₖ(1:Op J):=by
 obtain ⟨X,hX⟩:= CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr p)
 apply sub_nonneg.mp; rw [show Q⊗ₖ(1:Op J)-P⊗ₖ(1:Op J)= (Q-P)⊗ₖ(1:Op J) from (by simp [sub_eq_add_neg, Matrix.add_kronecker,op_kron_neg]),hX]
 have he:= star_mul_self_nonneg (X⊗ₖ (1:Op J)); rwa [op_star_kron,op_kron_mul,star_one,mul_one] at he -- tune hX direction
end Quad
end YM.CF.BPress.Spin

import YM.CF.Fock.Sphere

/-! Semigroup and anti-unit reflection. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Finset Function Filter NormedSpace
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n] [Fintype n]

def dg (A : Op n) := dyad A put takeF
lemma dg_add (A B : Op n) : dg (A+B)=dg A+dg B := dyad_plus ..
lemma dg_neg (A : Op n) : dg (-A)= -dg A := by simp only [dg,dyad,Matrix.neg_apply,neg_smul,sum_neg_distrib]
lemma dg_star (A : Op n) : dg (star A)=star (dg A) := by
  unfold dg dyad; rw [sum_comm]; simp only [star_sum,star_smul,star_mul,takeF,star_star]; rfl
lemma dg_scale (A : Op n) (c : ℝ) : dg (c • A)= c • dg A := by
  unfold dg dyad; simp only [Matrix.smul_apply,smul_sum,smul_assoc]
lemma dg_cov (A : Op n) (U : UNI n) : twist (quantU U) (dg A)=dg (twist U A) := by
  unfold dg; simp only [dyad_twist,twist_p,twist_t,dyad_prong,ccT]; rw [twist_formula]
lemma dg_clear (A : Op n) : cc (dg A)=dg (cc A) := by
  have he (t : Finset n) (f : n→FC n) : cc (∑ i∈t,f i)=∑ i∈t, cc (f i) := by ext i j; simp [Matrix.sum_apply]
  unfold dg dyad; simp_rw [he,cc_smul,cc_mul,put_clear,takeF,cc_star, put_clear]; rfl
lemma dg_diag (f : n→ℂ) : dg (Matrix.diagonal f)=Matrix.diagonal (fun s : Finset n=>∑ i∈s,f i) := by
  have he : dg (Matrix.diagonal f)=∑ i,f i • (put i*takeF i) := by
    unfold dg dyad; apply sum_congr rfl; intro i _; rw [sum_eq_single_of_mem _ (mem_univ i)]; simp; intro j _ h; simp [Ne.symm h]
  rw [he]; apply op_scale_column; intro i; rw [act_sum]
  simp_rw [act_smul,occ_act]; rw [← sum_subset (subset_univ i)]; swap; intro j _ h; rw [if_neg h,smul_zero]
  rw [Finset.sum_smul]; exact sum_congr rfl fun j h=> by rw [if_pos h]
lemma dg_skew (A : Op n) : twist (autumn n) (dg A)=A.trace • 1-dg Aᵀ := by
  have ht (i:n) : twist (autumn n) (takeF i)=put i := by rw [takeF,map_star,top_swap,takeF,star_star]
  simp only [dg,dyad,map_sum,twist_scalar,map_mul,top_swap,ht]
  have hp (i j:n) : takeF i*put j = (if i=j then 1 else 0)-put j*takeF i := eq_sub_of_add_eq (mixed ..)
  simp_rw [hp,smul_sub,sum_sub_distrib]; rw [sum_comm (f:=fun i j=>A i j • (put j*takeF i))]; congr 1; rw [Matrix.trace]; simp [apply_ite _ _,sum_ite_eq, sum_smul]
lemma theta_dg (U : UNI n) (A : Op n) : theta U (dg A)=star A.trace • 1 - dg (twist U (star A)) := by
  rw [theta,dg_clear,screenM, twin,dg_skew, ccT,map_sub,dg_cov,twist_scalar,map_one,invFilm,twin,rankPhase]; congr 2
  simp only [cc,Matrix.trace_transpose, Matrix.star_eq_conjTranspose,Matrix.trace_conjTranspose]
lemma dg_exp {A : Op n} (h : IsSelfAdjoint A) : exp (dg A) = quant (exp A) := by
  obtain ⟨U,d,rfl⟩ := spectral_exists A h; rw [spectral,←dg_cov,←breeze_exp, ←breeze_exp, quant_twist,phase_diag,quant_diag, dg_diag,phase_diag]
  apply congrArg; apply congrArg Matrix.diagonal; ext i : 1; simp [Function.comp_def, Complex.exp_sum]
lemma ferment {A : Op n} (h : IsSelfAdjoint A) (t : ℝ) : quant (grow A t)=exp (t • dg A) := by
  have he : IsSelfAdjoint (t • A) := by rw [isSelfAdjoint_iff]; simp only [star_smul,star_trivial,h.star_eq]
  rw [← dg_scale,grow]; exact (dg_exp he).symm
lemma pair_charge {S : Finset n} {A : Op n} (h : cutM S*A*cutM S=A) : Sector S false (dg A) := by
  unfold dg dyad; apply Sector.sumS; intro i _; apply Sector.sumS; intro j _
  have he : A i j=(if i∈S then 1 else (0:ℂ)) * A i j*(if j∈S then 1 else 0) := by nth_rw 1 [←h]; rw [cutM,Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases g:i∈ S ∧ j∈S
  · exact ((Sector.up _ g.1).mul (Sector.down _ g.2)).scale _
  rw [show A i j=0 from he.trans (by split_ifs <;> first | tauto | simp), zero_smul]; apply Sector.zero
lemma prizeUV (A B : Op n) : dg (A*star B)=∑ i,create (acts A (basisKet i))* remove (acts B (basisKet i)) := by
  unfold dg; rw [←mul_one A,←ccT B, ← dyad_prong 1 A (cc B)] -- removes occurrence?
  unfold dyad; simp_rw [prong_t,prong_p,mul_one]; simp [Matrix.one_apply,ite_smul] -- tune
end YM.CF.Fock

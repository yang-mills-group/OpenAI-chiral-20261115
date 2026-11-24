import YM.CF.Fock.Semig
/-! Triangular graph unipotent, exact exponential. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Finset NormedSpace Filter
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n]
lemma rake (i j k:n): put i*takeF j*put k-put k*(put i*takeF j)=if j=k then put i else 0:=by
  rw [mul_assoc,show takeF j*put k=_ from eq_sub_of_add_eq (mixed j k),mul_sub,←mul_assoc (put k),show put k*put i=_ from eq_neg_of_add_eq_zero_left (put_put ..),neg_mul,mul_assoc]; split <;> simp
lemma shelve (A:Op n)(i:n): dg A*put i-put i*dg A=create (acts A (basisKet i)):=by
  unfold dg dyad; simp_rw [mul_sum,sum_mul,←Finset.sum_sub_distrib,Algebra.mul_smul_comm, Algebra.smul_mul_assoc,←smul_sub,rake]; simp [create_def, basis_act,apply_ite _ _]
lemma lever (A:Op n)(x:Ket n): dg A*create x-create x*dg A=create (acts A x):=by
  nth_rw 1 2 [create_def]
  nth_rw 3 [←basis_expand x]
  simp_rw [mul_sum,sum_mul,map_sum,←sum_sub_distrib,map_smul,Algebra.mul_smul_comm, Algebra.smul_mul_assoc,←smul_sub,shelve]
lemma tact {a b d:FC n}(h:a*b-b*a=d)(g:a*d=d*a)(k:ℕ): a^(k+1)*b-b*a^(k+1)=(k+1:ℂ) • (d*a^k):=by
  induction k with
  | zero=>simp [h]
  | succ k ih=>
    have hf: a^(k+2)*b= (k+2:ℂ) • (d*a^(k+1))+b*a^(k+2):=by
      nth_rw 1 [pow_succ']; rw [mul_assoc, eq_add_of_sub_eq ih,mul_add,← mul_assoc a b, eq_add_of_sub_eq h,add_mul, Algebra.mul_smul_comm,← mul_assoc a d,g,mul_assoc d,pow_succ' a k,← pow_succ' a k]; -- tune
      have he : d*(a*a^k)=d*a^(k+1):=by rw [←pow_succ' a k];
      try rw [he]
      rw [mul_assoc b a,←pow_succ']; push_cast; simp [add_smul]; abel_nf; norm_num; simp [two_mul,two_smul,show (2:ℂ)=1+1 by norm_num,add_smul]
    apply sub_eq_iff_eq_add.mpr; push_cast; convert hf using 1; ring_nf
lemma calms (A: FC n) (B D:FC n) (h:A*B-B*A=D)(g:A*D=D*A): exp A*B=(B+D)*exp A:=by
  let P (i:ℕ): FC n:= (i.factorial:ℂ)⁻¹ • A^i; have he :Summable P:=(norm_expSeries_summable' (𝕂:=ℂ) A).of_norm
  let F(i:ℕ):=P i * B-B*P i; have hf:Summable F:=(he.mul_right B).sub (he.mul_left B)
  have ht (i): F (i+1)= D*P i:=by
    unfold F P; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc, ←smul_sub,tact h g,smul_smul, Nat.factorial_succ,Algebra.mul_smul_comm]; push_cast; congr 1; field_simp
  rw [show exp A=∑' i,P i from congrFun (exp_eq_tsum ℂ) A, add_mul, add_comm]
  apply eq_add_of_sub_eq
  rw [←Summable.tsum_mul_right B he, ←Summable.tsum_mul_left B he, ←(he.mul_right B).tsum_sub (he.mul_left B)]; -- tune
  change ∑' i,F i= D*_
  rw [← hf.sum_add_tsum_nat_add 1]; simp only [sum_range_one]; rw [show F 0=0 by simp [F,P], zero_add]; simp_rw [ht]; exact he.tsum_mul_left D
lemma pier {A:FC n}{v:Wave n}(h:acts A v=0): acts (exp A) v=v:=by
  let L:FC n→ₗ[ℂ] Wave n:=⟨⟨fun A:FC n=> acts A v,fun A B=>act_add ..⟩,fun c A=>act_smul ..⟩
  have he (A:FC n):L A=acts A v:=rfl
  rw [exp_eq_tsum ℂ]; dsimp only; rw [←he];
  let K:=L.toContinuousLinearMap; change K _=v; rw [K.map_tsum ((norm_expSeries_summable' (𝕂:=ℂ) A).of_norm),tsum_eq_single 0]; simp only [pow_zero,Nat.factorial_zero,Nat.cast_one,inv_one,one_smul]; exact act_one v
  intro i p; obtain ⟨k,rfl⟩:= Nat.exists_eq_succ_of_ne_zero p; change acts _ v=_; rw [pow_succ,act_smul,act_mul,h,map_zero,smul_zero]
lemma dg_veil(A:Op n): acts (dg A) (vacuum n)=0:=by
  unfold dg dyad; rw [act_sum]; apply sum_eq_zero; intro i _; rw [act_sum]; apply sum_eq_zero; intro j _; rw [act_smul,act_mul,← remove_take,vacuum_take,map_zero,smul_zero]
lemma tallied (A:Op n)(h:A*A=0): exp (dg A)=quant (1+A):=by
  apply quant_unique
  · exact pier (dg_veil A)
  intro i; apply (calms (dg A) (put i) _ (shelve A i) ?_).trans; -- should two goals reorder
  · rw [act_add,act_one,map_add,create_put]
  have he:=lever A (acts A (basisKet i)); rw [←act_mul,h,act_zero,map_zero] at he; exact sub_eq_zero.mp he
end YM.CF.Fock

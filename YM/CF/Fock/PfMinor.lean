import YM.CF.Fock.Laplace

/-! Coefficient square identity (all skew matrices). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Finset
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n] [Fintype n]
lemma line_quant_comm {S P : Op n} (h : S*P=P*S) : quant S*lineOp P=lineOp P*quant S := by
  rw [lineOp,← mul_assoc, ← quant_mul,h,quant_mul,mul_assoc,mul_assoc]
  simp_rw [sum_mul,mul_sum,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,selector_quant]
lemma row_unique {S : Op n} {s : Finset n} (h : S*cutM s=cutM s*S) (t : Finset n) (g : s ≠ t) : quant S s t=0 := by
  have he := line_quant_comm h; rw [cutLine,cutM] at he; have hx := Matrix.ext_iff.mpr he s t
  rw [Matrix.diagonal_mul,Matrix.mul_diagonal] at hx; exact (by simpa [g.symm] using hx.symm)
lemma transpose_cut {S : Op n} {s : Finset n} (h : S*cutM s=cutM s*S) : Sᵀ*cutM s=cutM s*Sᵀ := by
  nth_rw 1 2 [← self_t s]; rw [← Matrix.transpose_mul,←Matrix.transpose_mul,h]
lemma quant_transvol (A : Op n) (s : Finset n) : quant Aᵀ s s=quant A s s := by
  rw [principal,principal,show padded s Aᵀ=(padded s A)ᵀ by
    unfold padded; rw [Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_mul,Matrix.transpose_mul,self_t,mul_assoc,Matrix.transpose_one],Matrix.det_transpose]
lemma col_unique {S : Op n} {s : Finset n} (h : S*cutM s=cutM s*S) (t : Finset n) (g : s≠t) : quant S t s=0 := by
  have hg : star S*cutM s=cutM s*star S := by
    have H := congrArg star h; simp only [star_mul,(cutM_idp s).isSelfAdjoint.star_eq] at H; exact H.symm
  have h := row_unique hg t g; rw [quant_star] at h; simpa using h
lemma column_product {S : Op n} {s : Finset n} (h : S*cutM s=cutM s*S) (A : Op n) : quant (A*S) s s=quant A s s*quant S s s := by
  rw [quant_mul, Matrix.mul_apply,sum_eq_single_of_mem _ (mem_univ s)]; intro t _ ht; rw [col_unique h _ ht.symm,mul_zero]
lemma row_product {S : Op n} {s : Finset n} (h : S*cutM s=cutM s*S) (A : Op n) : quant (S*A) s s=quant S s s*quant A s s := by
  rw [quant_mul, Matrix.mul_apply,sum_eq_single_of_mem _ (mem_univ s)]; intro t _ ht; rw [row_unique h _ ht.symm,zero_mul]
lemma pf_frame {S : Op n} {s : Finset n} (h : S*cutM s=cutM s*S) (A : Op n) : pf (S*A*Sᵀ) s=quant S s s*pf A s := by
  rw [pf,pf,← pair_cov,act_at,Matrix.mulVec,dotProduct,sum_eq_single_of_mem _ (mem_univ s)]
  intro t _ ht; rw [row_unique h _ ht.symm,zero_mul]
lemma isolate {A : Op n} (g : Aᵀ= -A) {s : Finset n} {a b : n} (hx : b∈s) (hz : A a b≠0) :
    ∃ S : Op n, S*cutM s=cutM s*S ∧ (∃ T, S*T=1) ∧ ∀ i∈s, i ≠ b → (S*A*Sᵀ) a i=0 := by
  let f (i : n) := if i=b ∨ i∉s then 0 else - A a i / A a b
  let V : Op n := Matrix.of fun i j=> if j=b then f i else 0
  have he : f b=0 := by simp [f]
  let S := 1+V
  have ht : S*cutM s=cutM s*S := by
    unfold S; rw [add_mul,mul_add,one_mul,mul_one]; congr 1
    unfold cutM V; ext i j; rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]; by_cases h:i∈s <;> by_cases g:j=b <;> simp [f,h,g,hx]
  have hi : V*V=0 := by
    ext i j; rw [Matrix.mul_apply,sum_eq_zero]; rfl; intro k _; by_cases g:k=b <;> simp [V,g,f]
  refine ⟨S,ht,⟨1-V,?_⟩,?_⟩
  · unfold S; rw [add_mul,mul_sub V,hi,mul_one,sub_zero,one_mul]; abel
  have hA : f a=0 := by unfold f; split; rfl; rw [skew_diag A g,neg_zero,zero_div]
  have hZ (i) : (S*A) a i=A a i := by
    unfold S; rw [add_mul,one_mul,Matrix.add_apply, Matrix.mul_apply,sum_eq_zero,add_zero]; intro k _; simp [V,hA]
  intro i l hl; nth_rw 2 [show S=1+V from rfl]; rw [Matrix.transpose_add,Matrix.transpose_one, mul_add,mul_one, Matrix.add_apply,hZ, Matrix.mul_apply,sum_eq_single_of_mem _ (mem_univ b)]
  · rw [hZ,Matrix.transpose_apply]; simp only [V,Matrix.of_apply,ite_true, f,show ¬(i=b ∨ i∉s) from not_or.mpr ⟨hl, not_not.mpr l⟩,ite_false]; field_simp; ring
  intro k _ g; simp [V,g]
lemma pf_square (s : Finset n) (A : Op n) (g : Aᵀ= -A) : pf A s^2=quant A s s := by
  induction s using Finset.strongInductionOn generalizing A with
  | _ s ih =>
    by_cases e:s.Nonempty
    · obtain ⟨a,ha⟩ := e; by_cases h : ∃ b∈s,A a b≠0
      · obtain ⟨b,hb,f⟩ := h; have hk : b≠a := fun h=> f (by rw [h,skew_diag A g])
        obtain ⟨S,H,⟨T,hi⟩,hp⟩ := isolate g hb f; let B := S*A*Sᵀ
        have hg : Bᵀ= -B := skew_form g
        have hB : pf B s^2=quant B s s := by rw [match_pf _ hg _ _ _ ha hb hk hp, ih _ _ _ hg,matched _ hg _ _ _ ha hb hk hp]; exact lt_of_le_of_lt (erase_subset ..) (erase_ssubset ha)
        unfold B at hB; rw [pf_frame H,mul_pow,column_product (transpose_cut H),quant_transvol,row_product H,mul_right_comm _ _ (quant S _ _),←pow_two] at hB
        have he := row_product H T; rw [hi,quant_one,Matrix.one_apply_eq] at he
        exact mul_left_cancel₀ (pow_ne_zero _ (left_ne_zero_of_mul (by rw [←he]; exact one_ne_zero))) hB
      push Not at h
      have he := pf_spread _ g _ _ ha; rw [sum_eq_zero fun b hb => by rw [h b (mem_of_mem_erase hb),zero_mul]] at he
      rw [ (mul_eq_zero.mp he).resolve_left (by intro l; have H := parity_sq a s; rw [l,zero_mul] at H; exact zero_ne_one H), zero_pow (by omega),spread _ _ _ _ ha,sum_eq_zero,mul_zero]
      intro b l; rw [skew_swap A g, h b l,neg_zero,zero_mul]
    rw [not_nonempty_iff_eq_empty.mp e, quantum_at,wedge_empty,vacuum, basis_apply, if_pos rfl,pf,paired_vac,one_pow]
end YM.CF.Fock

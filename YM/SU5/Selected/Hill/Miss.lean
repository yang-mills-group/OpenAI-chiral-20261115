import YM.SU5.Selected.Chene.Melody
/-! Unsharp loss fine here weighted by omissions at deep free links. -/
set_option autoImplicit false
noncomputable section
namespace YM.Hill.Miss
open Function Filter Finset Matrix Chene.Melody
open scoped Topology BigOperators Classical MatrixOrder Matrix InnerProductSpace Kronecker
variable {I J K:Type*}[Fintype I][DecidableEq I][Fintype J][DecidableEq J][Fintype K][DecidableEq K]
variable {D: Matrix I I ℝ}{A:ℝ}
lemma meter (p:D.PosSemidef): D.det ≤ Real.exp D.trace:=by
 rw [p.isHermitian.trace_eq_sum_eigenvalues,p.isHermitian.det_eq_prod_eigenvalues,Real.exp_sum]; refine prod_le_prod (fun i _=>?_ ) fun i _=> ?_
 · exact p.eigenvalues_nonneg i
 let x:= p.isHermitian.eigenvalues i; change x≤Real.exp x; exact (by linarith only [Real.add_one_le_exp (p.isHermitian.eigenvalues i)])
lemma block_b (e: J⊕K≃I)(p:D.PosDef)(f:J→I)(t:∀ j, f j=e (.inl j))(h:∀ i,D i i ≤ A):
 D.det ≤ (D.submatrix f f).det * Real.exp ((Fintype.card K :ℝ)*A) :=by
 let g(j:K):=e (.inr j); let M:= D.submatrix f f; let Z:=D.submatrix e e; let W:= D.submatrix g g; let U:= D.submatrix f g
 have hf: f.Injective:=by rw [funext (g:=e∘Sum.inl) t]; exact e.injective.comp Sum.inl_injective
 have hp:M.PosDef:=p.submatrix hf
 letI : Invertible M:=hp.isUnit.invertible
 let Q:= Uᴴ*M⁻¹*U
 have he:Z= fromBlocks M U Uᴴ W:=by
    ext a b; have hx:Dᴴ=D:= p.isHermitian.eq; have hh(y z):D y z=D z y:=Matrix.ext_iff.mpr (isHermitian_iff_isSymm.mp p.isHermitian) z y -- tune
    obtain a|a:=a<;> obtain b|b:=b<;> simp [Z,M,W,g,U,t,hh]
 have hQ: (W-Q).PosSemidef := (PosDef.fromBlocks₁₁ _ _ hp).mp (he ▸ (show Z.PosSemidef from p.posSemidef.submatrix _))
 have hX: W-Q≤ W := sub_le_self W (hp.inv.posSemidef.conjTranspose_mul_mul_same U |>.nonneg)
 rw [← det_submatrix_equiv_self e]; change Z.det ≤ _; rw [he,det_fromBlocks₁₁,invOf_eq_nonsing_inv]
 apply mul_le_mul_of_nonneg_left _ hp.det_pos.le; apply (det_rise hQ hX).trans; apply (meter (p.posSemidef.submatrix g)).trans; apply Real.exp_monotone
 exact (sum_le_sum (g:=fun _=> A) (fun i _=> h (g i))).trans_eq (by simp)
lemma scale_b (S: Matrix J J ℝ)(q r:ℝ)(Q q': Matrix I I ℝ)(h:Q.PosDef)(z:0<q)(w:q^2 • Q ≤ q')(A:ℝ)(p:S.det ≤ Q.det * Real.exp A)(u: q • q'= D) : D.PosDef ∧ S.det ≤ Real.exp A / ((q^3)^Fintype.card I) * D.det:=by
 have hv:q^3 • Q ≤ D:=by
    rw [←u]; have hy:= (Matrix.le_iff.mp w).smul z.le; rw [smul_sub,smul_smul, ←pow_succ'] at hy; exact Matrix.le_iff.mpr hy
 have hB:=h.smul (pow_pos z 3); refine ⟨pay_c hB hv,p.trans ?_⟩
 rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0< (q^3)^Fintype.card I)]; have he:=(det_rise hB.posSemidef hv); rw [det_smul] at he; nlinarith only [mul_le_mul_of_nonneg_left he (Real.exp_pos A |>.le)]
end YM.Hill.Miss
#print axioms YM.Hill.Miss.block_b

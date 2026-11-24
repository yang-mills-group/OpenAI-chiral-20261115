/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Fineness.Hodge
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.Fineness
open Function Matrix Finset
open scoped Matrix MatrixOrder -- don't import Frobenius to avoid CS
variable {I J : Type*}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{A B : Sheet I}{X:Tab I J}
lemma qpos {g:ℝ}(h:g>0)(u:Aᵀ=A)(p:FreeResolvent.Gap A g): A.PosDef:= (q_iff A).2 ⟨u,fun _ v=> (mul_pos h (l2pos _ v)).trans_le (p.lower _)⟩
lemma rates (r:ℝ)(X:Sheet I)(x:I →ℝ):qpay (r • X) x=r*qpay X x:=by unfold qpay; rw [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
lemma one_eigen (h:B.PosDef)(p:∀ x,qpay (1:Sheet I) x≤ qpay B x) : ∀ i,(1:ℝ) ≤ h.isHermitian.eigenvalues i:=by
 intro i; let H:=h.isHermitian; let Y:I→ℝ:= ⇑(H.eigenvectorBasis i)
 have he:=H.eigenvalues_eq i; change _ = RCLike.re (dotProduct (star Y) _) at he; rw [star_trivial] at he
 have ht:qpay (1:Sheet I) Y=1:=by
    unfold qpay; rw [one_mulVec]; nth_rw 2 [← star_trivial Y]; rw [← EuclideanSpace.inner_eq_star_dotProduct (x:= (H.eigenvectorBasis i)) (y:= (H.eigenvectorBasis i)),real_inner_self_eq_norm_sq,(H.eigenvectorBasis.orthonormal.1 i),one_pow]
 exact ht ▸ (p Y).trans_eq (Eq.symm (show H.eigenvalues i=qpay B Y from he)) -- tune
lemma uncle (h:A.PosDef): ∃ (T:Sheet I), IsUnit T ∧ Tᵀ*A*T=1:=by
 let B:= CFC.sqrt A
 have he:B*B=A:= CFC.sqrt_mul_sqrt_self _ h.posSemidef.nonneg
 have hp:Bᵀ=B:= Matrix.isHermitian_iff_isSymm.mp (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
 have hv:IsUnit B.det:=by
    have hA:=h.det_pos; apply isUnit_iff_ne_zero.mpr; intro k; rw [← he,det_mul,k,mul_zero] at hA; exact lt_irrefl 0 hA
 refine ⟨B⁻¹,isUnit_iff_isUnit_det _ |>.2 (Matrix.isUnit_nonsing_inv_det B hv),?_⟩
 rw [Matrix.transpose_nonsing_inv, hp, ← he, ← Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hv,Matrix.one_mul, Matrix.mul_nonsing_inv _ hv]

lemma harvested (t:A.PosDef)(u:Bᵀ=B)(p:∀ x,qpay A x ≤ qpay B x) : B.PosDef∧ A.det≤B.det:=by
 obtain ⟨T,h,e⟩:= uncle t; let D:= Tᵀ*B*T; have hx:Dᵀ=D:=by unfold D; rw [transpose_mul,transpose_mul,u,transpose_transpose, Matrix.mul_assoc]
 have ht: B.PosDef:=(q_iff B).2 ⟨u,fun x y=>(q_at A t y).trans_le (p x)⟩; have hf(x:I→ℝ) : qpay 1 x≤ qpay D x:=by
    unfold D; rw [←e,qgain,qgain]; exact p _
 have hd:D.PosDef:= (q_iff D).2 ⟨hx,fun x p=>(q_at 1 Matrix.PosDef.one p).trans_le (hf x)⟩
 have hs:1 ≤ D.det:=by
    rw [hd.isHermitian.det_eq_prod_eigenvalues]
    exact one_le_prod fun i _ => (one_eigen hd hf) i
 have hv0:T.det≠0:= isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det _).mp h)
 have hA : det T *det T *det A=1:= by rw [show det T * det T * det A=det (Tᵀ*A*T) by simp [det_mul]; ring,e,det_one]; -- tune
 unfold D at hs; rw [det_mul,det_mul,det_transpose,←hA] at hs
 exact ⟨ht,le_of_mul_le_mul_left (hs.trans_eq (by ring)) (show 0<det T*det T from (sq (det T)) ▸ sq_pos_of_ne_zero hv0)⟩ -- tune

lemma volume_ceiling (h:A.PosDef): Real.log A.det ≤ A.trace :=by
 let H:=h.isHermitian; rw [H.trace_eq_sum_eigenvalues,H.det_eq_prod_eigenvalues]; change Real.log (∏ i,H.eigenvalues i) ≤ ∑ i,H.eigenvalues i; rw [Real.log_prod (fun i _=>(h.eigenvalues_pos _).ne')]
 apply sum_le_sum; intro i _; exact (Real.log_le_sub_one_of_pos (h.eigenvalues_pos _)).trans (sub_le_self _ zero_le_one)
lemma open_volume (h:ZeroBasis A X) : (A+X* Xᵀ).det=torsion A X * ((Xᵀ * X).det)^2:=by
 let P:=Xᵀ * X; let R:=P⁻¹* Xᵀ; let B:=P*P
 have hs:Pᵀ=P:=by unfold P; simp; -- type
 have hp:IsUnit P.det:= (isUnit_iff_ne_zero.mpr ((h.rail.gramPos.det_pos).ne'))
 have hi:R*X=1:=by unfold R; rw [Matrix.mul_assoc]; exact Matrix.nonsing_inv_mul _ hp
 have hn:P* R=Xᵀ:=by unfold R; rw [← Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hp,Matrix.one_mul]
 rw [h.reels hi]
 let T:= 1+ X*(B-1)*R; have hx:T.det=B.det:=by unfold T; rw [Matrix.mul_assoc, det_one_add_mul_comm,Matrix.mul_assoc,hi,Matrix.mul_one]; congr 1; abel
 have hy:A*T=A:=by unfold T; rw [Matrix.mul_add,Matrix.mul_one,← Matrix.mul_assoc,← Matrix.mul_assoc A X,h.nullA]; simp
 have hg:R*T=B*R:=by unfold T; rw [Matrix.mul_add, Matrix.mul_one,←Matrix.mul_assoc,← Matrix.mul_assoc R X,hi,Matrix.one_mul,Matrix.sub_mul B 1 R]; simp
 have hL:Rᵀ*P=X:=by rw [show Rᵀ*P=(P*R)ᵀ by rw [transpose_mul P R,hs],hn]; simp
 rw [show A+X*Xᵀ = (A+Rᵀ*R)*T from ?_,det_mul,hx]; unfold B; rw [det_mul,sq]
 rw [Matrix.add_mul,hy,Matrix.mul_assoc Rᵀ R,hg, ← Matrix.mul_assoc Rᵀ]; unfold B; rw [← Matrix.mul_assoc Rᵀ, hL,Matrix.mul_assoc,hn]

section
variable {C D:Sheet I}
lemma pen_left (g:ℝ)(p:g>0)(u:C.PosDef): (g • C).PosDef:= (q_iff _).2 ⟨ by rw [transpose_smul,((q_iff C).1 u).1], fun x v=> (rates g C x) ▸ mul_pos p (q_at C u v)⟩

/-! if difference X of symmetric matrices bounded in ℓ∞ row max, adapted estimate (schur).
 Future. -/
end
end YM.Fineness
#print axioms YM.Fineness.harvested
#print axioms YM.Fineness.open_volume

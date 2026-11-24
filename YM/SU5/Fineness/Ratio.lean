import YM.SU5.Fineness.Vertical
/-! # Partial tree slice ratio toolkit -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
noncomputable section
set_option linter.unusedSectionVars false
namespace YM.Fineness
open Function Finset Matrix
open scoped Matrix
variable {I J K L V : Type*} [DecidableEq I][Fintype I][DecidableEq J][Fintype J][DecidableEq K][Fintype K][DecidableEq L][Fintype L][DecidableEq V][Fintype V]
lemma gramdet_reverse (A:Tab I J)(U:Tab J I)(e:I≃J) : (A*U).det=(U*A).det:=by
  let X:=A.submatrix id e; let Y:=U.submatrix e id
  rw [show A*U=X*Y by unfold X Y; rw [submatrix_mul_equiv]; rfl,←det_submatrix_equiv_self e,show (U*A).submatrix e e=Y*X from ?_]
  · apply det_mul_comm
  exact (submatrix_mul_equiv _ _ _ (Equiv.refl _) _).symm -- tune args order

variable {A: Sheet I}{B:Sheet J}
namespace ZeroBasis
lemma sloped_quote {X:Tab I K}(h:ZeroBasis A X)(P:Sheet J)(t:Pᵀ=P)(Q:Tab J I) : let W:=A+Qᵀ*P*Q; let D:= -(Qᵀ*P); let M:=fromBlocks W D Dᵀ P; let R:=fromRows X (Q*X); ZeroBasis M R ∧ torsion M R=torsion A X*P.det:=by
  intro W D M R
  have hg:=h.lift_sloped P t Q; simp only at hg; rw [fromBlocks_transpose,fromBlocks_multiply,fromBlocks_multiply] at hg
  unfold M W D R; simpa only [transpose_one,transpose_zero,Matrix.one_mul,Matrix.mul_one, Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add,transpose_neg,transpose_mul,t,transpose_transpose,Matrix.mul_neg,Matrix.neg_mul,neg_neg] using hg

omit [DecidableEq V] [DecidableEq K] in
private lemma door(E: Type*)[DecidableEq E][Fintype E](D:Tab I K)(Z:Tab I V)(R:Tab K I)(S:Tab V I) (v:D*R+Z*S=1) :
   let T':=fromCols (fromRows D (0:Tab E K)) (fromBlocks Z 0 0 (1:Sheet E)); let U':= fromRows (fromCols R (0:Tab K E)) (fromBlocks S 0 0 (1:Sheet E))
   T'*U'=1:=by
  intro T U; unfold T U; rw [fromCols_mul_fromRows,fromRows_mul_fromCols,fromBlocks_multiply,fromBlocks_add]; simp [v,fromBlocks_one]
private lemma facing(E: Type*)[DecidableEq E][Fintype E](D:Tab I K)(R:Tab I V) :
 (fromCols (fromRows D (0:Tab E K)) (fromBlocks R 0 0 (1:Sheet E)) * (fromCols (fromRows D (0:Tab E K)) (fromBlocks R 0 0 (1:Sheet E)))ᵀ ).det=(fromCols D R*(fromCols D R)ᵀ).det:=by
  rw [transpose_fromCols,transpose_fromRows,fromBlocks_transpose,fromCols_mul_fromRows,fromRows_mul_fromCols,fromBlocks_multiply,fromBlocks_add]
  simp only [transpose_zero,transpose_one,Matrix.zero_mul,Matrix.mul_zero,zero_add,add_zero,Matrix.one_mul]; rw [det_fromBlocks_zero₁₂,det_one,mul_one,transpose_fromCols,fromCols_mul_fromRows]

/-- Relative free-pressure via saddle with partial deep leaves. -/
lemma siege (D : Tab I K)(Y : Tab I L) (h:ZeroBasis A (fromCols D Y)) (e:(K⊕V)≃ I)
    (R:Tab I V)(U:Tab (K⊕V) I) (g: fromCols D R * U=1) (P: Sheet J)(t:Pᵀ=P)(Q:Tab J I)(f:Q*D=0) : let G:=Rᵀ*(A+Qᵀ*P*Q)*R; let K' := -(Rᵀ*Qᵀ*P); let T:=fromCols D R
    ∀ L': Tab V J,G*L'+K'=0→ IsUnit G → ZeroBasis (K'ᵀ*L'+P) (Q*Y) ∧ (T*Tᵀ).det*(torsion A (fromCols D Y)*P.det)=G.det*torsion (K'ᵀ*L'+P) (Q*Y):=by
  intro Z A' T L p l
  let W:= A+Qᵀ*P*Q; let B:= -(Qᵀ*P); let M:=fromBlocks W B Bᵀ P
  let D':=fromRows D (0:Tab J K); let Y':=fromRows Y (Q*Y); let R':=fromBlocks R 0 0 (1:Sheet J); let T':=fromCols D' R'; let U':=fromRows (fromCols (toRows₁ U) (0:Tab K J)) (fromBlocks (toRows₂ U) 0 0 (1:Sheet J))
  let V':= fromRows ((toRows₂ U)*Y) (Q*Y)
  have hx: toRows₂ (U'*Y')= V':=by unfold U' Y' V'; rw [fromRows_mul,toRows₂_fromRows,fromBlocks_mul_fromRows]; simp
  have he : T'*U'=1:=by
    apply door; nth_rw 1 [← fromRows_toRows U] at g; rwa [fromCols_mul_fromRows] at g
  let e':= (Equiv.sumAssoc ..).symm.trans (Equiv.sumCongr e (Equiv.refl J)); have hh: U'*T'=1:= (mul_eq_one_comm_of_equiv e'.symm).mp he
  have hv: (fromCols D' Y')=fromRows (fromCols D Y) (Q*(fromCols D Y)):=by unfold D' Y'; rw [mul_fromCols,f]; exact (fromCols_fromRows_eq_fromBlocks ..).trans (fromRows_fromCols_eq_fromBlocks ..).symm
  obtain ⟨hp,hb⟩:= h.sloped_quote P t Q; have hM:ZeroBasis M (fromCols D' Y'):= hv.symm ▸ hp
  have hw: (R')ᵀ*M*R'= fromBlocks Z A' A'ᵀ P:=by unfold R' M B Z A'; rw [fromBlocks_transpose,fromBlocks_multiply,fromBlocks_multiply]; simp only [transpose_zero,transpose_one,Matrix.mul_zero,Matrix.zero_mul,Matrix.one_mul,Matrix.mul_one,add_zero,zero_add]; unfold W; rw [transpose_neg,transpose_mul,transpose_transpose]; simp [transpose_mul,t,Matrix.mul_assoc]
  obtain ⟨hX,hY⟩:= hM.slice R' (T:=T') rfl e' U' he hh
  rw [hw,hx] at hX hY; obtain ⟨Hy,u⟩:=eliminated hX L p l -- eta state
  refine ⟨Hy,?_⟩; rw [hv, (gramdet_reverse _ _ e'),show (T'*T'ᵀ).det=(T*Tᵀ).det from facing J D R, hb] at hY -- e order
  exact hY.symm.trans u
end ZeroBasis
end YM.Fineness
#print axioms YM.Fineness.ZeroBasis.siege

import YM.SU5.Fineness.Covolume
/-!
# Vertical resolution including PARTIAL freedom in null space
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.Fineness
open Function Finset Matrix
open scoped Matrix
variable {I J K L V : Type*} [DecidableEq I][Fintype I][DecidableEq J][Fintype J][DecidableEq K][Fintype K][DecidableEq L][Fintype L][DecidableEq V][Fintype V]
variable {A: Sheet I}{B:Sheet J}
namespace ZeroBasis
lemma null_pair {X:Tab I K}{Y:Tab I L} (h:ZeroBasis A (fromCols X Y)): A*X=0 ∧ A*Y=0:=fromCols_inj (by rw [← mul_fromCols,h.nullA]; exact fromCols_zero.symm)

/-- Free internal gauge slice, paying Jacobian. Remaining null directions
    descend via projection along these.
 -/
lemma slice {X:Tab I K}{Y:Tab I L} (h:ZeroBasis A (fromCols X Y)) (R:Tab I J) {T:Tab I (K⊕J)} (hm : T=fromCols X R) (e : (K⊕J) ≃ I) (U:Tab (K⊕J) I) (v: T*U=1)(p:U*T=1) :
    ZeroBasis (Rᵀ*A*R) (toRows₂ (U*Y)) ∧ torsion (Rᵀ*A*R) (toRows₂ (U*Y))=(Tᵀ*T).det*torsion A (fromCols X Y):=by
  subst T; let T:=fromCols X R
  let P:=toRows₁ (U*Y); let Q:=toRows₂ (U*Y); let W:=fromBlocks (1:Sheet K) P (0:Tab J K) Q
  let B:=Rᵀ*A*R
  let F:=fromBlocks (0:Sheet K) 0 0 B
  have hz:T*W=fromCols X Y:=by
    unfold T W; rw [fromCols_mul_fromBlocks]; simp only [Matrix.mul_one,Matrix.mul_zero,add_zero]
    rw [← fromCols_mul_fromRows]; unfold P Q; rw [fromRows_toRows, ←Matrix.mul_assoc,v,Matrix.one_mul]
  have hF:Tᵀ*A*T=F:=by
    have hx:Xᵀ*A=0:=by nth_rw 1 [←h.symmA]; rw [←transpose_mul,h.null_pair.1]; rfl
    unfold T F B; rw [transpose_fromCols,fromRows_mul,hx,fromRows_mul_fromCols,Matrix.zero_mul,Matrix.zero_mul,Matrix.mul_assoc, h.null_pair.1,Matrix.mul_zero]
  have hu:= h.petition T U hz v p; rw [hF] at hu
  let S:=fromBlocks (1:Sheet K) (-P) 0 (1:Sheet L); let D:=fromBlocks (1:Sheet K) P 0 (1:Sheet L); let Z:= fromBlocks (1:Sheet K) (0:Tab K L) (0:Tab J K) Q
  have hd:D*S=1:=by unfold D S; rw [fromBlocks_multiply]; simp [fromBlocks_one]
  have hc:S*D=1:=(mul_eq_one_comm).mp hd
  have hs:W*S=Z:=by unfold W S Z; rw [fromBlocks_multiply]; simp
  have he:S.det=1:=by unfold S; rw [det_fromBlocks_zero₂₁]; simp
  have hp':=hu.slide_basis S D hc hd hs; obtain ⟨C,g⟩:=hp'.rail
  have hb: (toBlocks₂₂ C)*Q=1:=by
    unfold Z at g
    nth_rw 1 [← fromBlocks_toBlocks C] at g; rw [fromBlocks_multiply,← fromBlocks_one] at g
    simpa using (fromBlocks_inj.mp g).2.2.2
  have hB: ZeroBasis B Q:= ⟨by unfold B; rw [transpose_mul,transpose_mul,h.symmA,Matrix.mul_assoc,transpose_transpose],?_,⟨_,hb⟩⟩
  ·
    refine ⟨hB,?_⟩
    rw [←h.resize T U e hz v p,hF, hu.basis_expense (Equiv.refl _) S D hc hd hs]; rw [det_mul,det_transpose,he,one_mul,one_mul,joint_bill (filled K) hB,paid,one_mul]
  have hg:=hp'.nullA; unfold Z F at hg; rw [fromBlocks_multiply] at hg
  suffices h: fromBlocks (0:Sheet K) (0:Tab K L) (0:Tab J K) (B*Q) = 0 by
    exact (fromBlocks_inj.mp (h.trans fromBlocks_zero.symm)).2.2.2
  simpa only [Matrix.mul_zero,Matrix.zero_mul,zero_add] using hg

lemma lift_sloped {X:Tab I K}(h:ZeroBasis A X)(P:Sheet J)(t:Pᵀ=P)(D:Tab J I) : let U:=fromBlocks (1:Sheet I) (0:Tab I J) (-D) (1:Sheet J)
    let F:=Uᵀ*(fromBlocks A 0 0 P)*U; let Y:= fromRows X (D*X)
    ZeroBasis F Y ∧ torsion F Y=torsion A X * P.det :=by
  intro U F Y; let V:= fromBlocks (1:Sheet I) (0:Tab I J) D (1:Sheet J)
  have hv:U*V=1:=by unfold U V; rw [fromBlocks_multiply]; simp [fromBlocks_one]
  have he: U*Y=fromRows X 0:=by unfold U Y; rw [fromBlocks_mul_fromRows]; simp
  have hg:=h.split_right P t; have hw: U.det=1:=by unfold U; rw [det_fromBlocks_zero₁₂,det_one, det_one,mul_one]
  refine ⟨hg.petition U V he hv (mul_eq_one_comm.mp hv),?_⟩
  unfold F; rw [hg.resize U V (Equiv.refl _) he hv (mul_eq_one_comm.mp hv),det_mul,det_transpose,hw,one_mul,one_mul,h.right_bill P t]

/-- Vertical integration, including action on the nullspace. -/
lemma eliminated {P:Tab I J}{X:Tab I K}{Y:Tab J K} (h:ZeroBasis (fromBlocks A P Pᵀ B) (fromRows X Y)) (U: Tab I J) (p:A*U+P=0) (v:IsUnit A) : ZeroBasis (Pᵀ*U+B) Y ∧
    torsion (fromBlocks A P Pᵀ B) (fromRows X Y)=A.det*torsion (Pᵀ*U+B) Y:=by
  let T:=fromBlocks (1:Sheet I) U (0:Tab J I) (1:Sheet J); let S:=fromBlocks (1:Sheet I) (-U) (0:Tab J I) (1:Sheet J); let D:=Pᵀ*U+B
  let F:=fromBlocks A P Pᵀ B
  have he: T*S=1:=by unfold S T; rw [fromBlocks_multiply]; simp [fromBlocks_one]
  have ht: Tᵀ*F*T=fromBlocks A 0 0 D:=by
    have ha:= congrArg transpose p; rw [transpose_add,transpose_mul] at ha
    have hx:=h.symmA; rw [fromBlocks_transpose] at hx; rw [(fromBlocks_inj.mp hx).1] at ha
    unfold T F; rw [Matrix.mul_assoc Tᵀ,fromBlocks_multiply, fromBlocks_transpose,fromBlocks_multiply]; simp [p,show Uᵀ*A+Pᵀ=0 from ha,D]
  let R:=fromRows X Y; have hx:T*(fromRows (0:Tab I K) Y)=R:=by
    have hg:=h.nullA; rw [fromBlocks_mul_fromRows] at hg
    have hh: A*X+P*Y=0:= (fromRows_inj (hg.trans fromRows_zero.symm)).1; have hw: (A*U)*Y= A*X:= by rw [eq_neg_of_add_eq_zero_left p,Matrix.neg_mul,eq_neg_of_add_eq_zero_left hh];
    rw [Matrix.mul_assoc A U Y] at hw
    unfold R; rw [show X=U*Y from ?_] -- inside R defeq?
    ·
      unfold T; rw [fromBlocks_mul_fromRows]; simp
    let hL:= Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det _).mp v)
    calc _=A⁻¹*(A*X):=by rw [←Matrix.mul_assoc,hL,Matrix.one_mul]
         _=_:=by rw [← hw,←Matrix.mul_assoc A⁻¹, hL, Matrix.one_mul]
  have hg:=h.petition T S hx he (mul_eq_one_comm.mp he); rw [ht] at hg; have hD:Dᵀ=D:=(fromBlocks_inj.mp ((fromBlocks_transpose ..).symm.trans hg.symmA)).2.2.2
  have hu: D*Y=0:=by
    have hY:=hg.nullA; rw [fromBlocks_mul_fromRows] at hY; simpa using (fromRows_inj (hY.trans fromRows_zero.symm)).2
  have hy:ZeroBasis D Y:=by
    obtain ⟨C,g⟩:=hg.rail
    refine ⟨hD,hu,toCols₂ C,?_⟩
    nth_rw 1 [← fromCols_toCols C] at g; rw [fromCols_mul_fromRows,Matrix.mul_zero,zero_add] at g; exact g
  refine ⟨hy,?_⟩; have hA:=h.resize T S (Equiv.refl _) hx he (mul_eq_one_comm.mp he); rw [ht, hy.left_bill A ((fromBlocks_inj.mp ((fromBlocks_transpose ..).symm.trans (h.symmA))).1)] at hA
  rw [det_mul,det_transpose,show T.det=1 by unfold T; rw [det_fromBlocks_zero₂₁]; simp,one_mul,one_mul] at hA; exact hA.symm
end ZeroBasis
end YM.Fineness
#print axioms YM.Fineness.ZeroBasis.eliminated
#print axioms YM.Fineness.ZeroBasis.slice

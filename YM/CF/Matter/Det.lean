import YM.CF.Matter.Wedge

/-! Determinant of the antisymmetric representation. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.ExTwo
open scoped Matrix BigOperators
open Finset
variable {n : Type*} [Fintype n] [LinearOrder n]

lemma wedge_diag (d : n → ℂ) : wedgeOp (Matrix.diagonal d) = Matrix.diagonal (fun p : Idx n => d p.val.1 * d p.val.2) := by
  ext p q
  rw [wedge_entry]
  have h : Matrix.diagonal d p.val.1 q.val.2 * Matrix.diagonal d p.val.2 q.val.1 = 0 := by
    by_cases e:p.val.1=q.val.2
    · have he : p.val.2 ≠ q.val.1 := ne_of_gt <| calc
        q.val.1 < q.val.2 := q.property
        _ = _ := e.symm
        _ < _ := p.property
      simp [he]
    simp [e]
  rw [h,sub_zero]; by_cases e:p=q
  · simp [e]
  rw [Matrix.diagonal_apply_ne _ e]; by_cases ha:p.val.1=q.val.1
  · have hb : p.val.2≠q.val.2 := fun H => e (Subtype.ext (Prod.ext ha H)); simp [hb]
  simp [ha]
lemma wedge_diag_det (d : n → ℂ) : (wedgeOp (Matrix.diagonal d)).det = ((Matrix.diagonal d).det)^(Fintype.card n-1) := by
  rw [wedge_diag,Matrix.det_diagonal, Matrix.det_diagonal]
  let S := univ.filter fun x:n×n => x.1<x.2
  have he := prod_subtype (p:=fun x:n×n => x.1<x.2) (F:=(inferInstance : Fintype (Idx n))) S (by simp [S]) (fun x => d x.1*d x.2)
  rw [← he, prod_mul_distrib,show ∏ x∈S, d x.2 = ∏ x∈univ.filter (fun x:n×n => x.2<x.1), d x.1 by
    refine prod_bij' (fun x _ => x.swap) (fun x _ => x.swap) (fun _ _ => ?_) (fun _ _ => ?_) (by simp) (by simp) (by simp)
    all_goals simp_all [S]]
  unfold S
  rw [prod_filter, prod_filter, ← prod_mul_distrib, Fintype.prod_prod_type, ← prod_pow]
  refine prod_congr rfl fun x _ => ?_
  simp only
  calc
    _ = ∏ y ∈ (@univ n _).erase x, d x := by
      have ho : (@univ n _).erase x = univ.filter (· ≠ x) := by ext; simp
      rw [ho,prod_filter]
      refine prod_congr rfl fun y _ => ?_
      rcases lt_trichotomy x y with h|h|h
      · simp [h,h.asymm,Ne.symm h.ne]
      · simp [h]
      simp [h,h.asymm,h.ne]
    _ = _ := by simp

lemma wedge_det_trans (i j : n) (h : i≠j) (c : ℂ) :
    (wedgeOp (Matrix.transvection i j c)).det=1 := by
  let T := Matrix.transvection i j c
  have hin := Matrix.transvection_mul_transvection_same i j h c (-c)
  rw [add_neg_cancel,Matrix.transvection_zero] at hin
  have hi := congrArg (fun A => (wedgeOp A).det) hin
  simp only [wedge_mul,wedge_one, Matrix.det_one,Matrix.det_mul] at hi
  have hn : (wedgeOp T).det ≠ 0 := by intro hz; change (wedgeOp T).det*_=_ at hi; rw [hz,zero_mul] at hi; exact zero_ne_one hi
  let d : n→ℂ := fun x => if x=i then 2 else 1
  have hv : (wedgeOp (Matrix.diagonal d)).det ≠ 0 := by
    rw [wedge_diag_det,Matrix.det_diagonal]
    exact pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun a _ => by dsimp only [d]; split <;> norm_num)
  have hh : Matrix.diagonal d * T = (T*T) * Matrix.diagonal d := by
    unfold T
    rw [Matrix.transvection_mul_transvection_same i j h c c]
    ext x y; rw [Matrix.diagonal_mul, Matrix.mul_diagonal]; simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply,Matrix.one_apply]
    by_cases ha:x=y
    · rw [mul_comm (d x)]; subst y; simp [(show ¬(i=x∧j=x) from fun ⟨e,f⟩ => h (e.trans f.symm))]
    by_cases he:i=x∧j=y
    · rcases he with ⟨rfl,rfl⟩; simp only [if_neg h,d,if_neg (Ne.symm h), and_self_iff,↓reduceIte]; ring
    simp [ha,he]
  have hw := congrArg (fun A => (wedgeOp A).det) hh
  simp only [wedge_mul,Matrix.det_mul] at hw
  rw [mul_comm (Matrix.det (wedgeOp (Matrix.diagonal d)))] at hw
  have hj := mul_right_cancel₀ hv hw
  apply mul_left_cancel₀ hn
  rw [mul_one]; exact hj.symm

theorem wedge_det (A : Op n) : (wedgeOp A).det=A.det^(Fintype.card n-1) := by
  apply Matrix.diagonal_transvection_induction _ A (fun D _ => wedge_diag_det D) (fun t => ?_) (fun B C h g => ?_)
  · rw [t.det,one_pow]; exact wedge_det_trans t.i t.j t.hij t.c
  rw [wedge_mul,Matrix.det_mul,h,g,Matrix.det_mul,mul_pow]
end YM.CF.ExTwo

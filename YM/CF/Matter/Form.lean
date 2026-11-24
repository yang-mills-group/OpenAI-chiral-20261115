import YM.CF.Matter.Rep

/-! SU5 volume tensor on actual wedge pair. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.ExTwo
open scoped Matrix BigOperators
open Finset
variable {n : Type*} [Fintype n] [LinearOrder n]

/-- Wedge of two columns. -/
def exterior (v w : n → ℂ) : Idx n → ℂ := fun x => v x.val.1 * w x.val.2 - v x.val.2 * w x.val.1
lemma alternSum (B : n×n → ℂ) (hb : ∀ i, B i.swap= -B i) (hz : ∀ i, B (i,i)=0) (v w : n→ℂ) :
    ∑ i:n, ∑ j:n, v i*w j*B (i,j) = ∑ x:Idx n, exterior v w x * B x.val := by
  let F := fun x:n×n => (v x.1*w x.2)*B x
  let T := (univ:Finset (n×n)).filter fun x => x.1<x.2
  let S := (univ:Finset (n×n)).filter fun x => x.2<x.1
  have hsub := sum_subtype T (p:=fun x:n×n => x.1<x.2) (F:=(inferInstance:Fintype (Idx n))) (by simp [T])
    (fun x => F x + F x.swap)
  calc
    _ = ∑ x : n×n, F x := (Fintype.sum_prod_type F).symm
    _ = ∑ x∈T, F x + ∑ x∈S, F x := by
      dsimp only [T,S]; rw [sum_filter,sum_filter, ← sum_add_distrib]
      apply sum_congr rfl; rintro ⟨i,j⟩ _
      rcases lt_trichotomy i j with h|h|h
      · simp [h,h.asymm]
      · simp [h,F,hz]
      simp [h,h.asymm]
    _ = ∑ x∈T, F x + ∑ x∈T, F x.swap := by
      congr 1
      refine sum_bij' (fun x _ => x.swap) (fun x _ => x.swap) ?_ ?_ (by simp) (by simp) (by simp) <;> simp [S,T]
    _ = _ := by
      rw [← sum_add_distrib,hsub]; apply sum_congr rfl; intro x _
      unfold F exterior; rw [hb]; simp only [Prod.fst_swap,Prod.snd_swap]; ring
lemma exterior_action (A : Op n) (v w : n → ℂ) : wedgeOp A *ᵥ exterior v w = exterior (A*ᵥ v) (A*ᵥ w) := by
  funext p
  let B := fun x:n×n => A p.val.1 x.1*A p.val.2 x.2 - A p.val.1 x.2 * A p.val.2 x.1
  have he := alternSum B (fun x => by dsimp [B]; ring) (fun _ => by simp [B]) v w
  change ∑ x:Idx n, B x.val * exterior v w x = _
  rw [show (∑ x:Idx n,B x.val*exterior v w x)=_ by simp_rw [mul_comm (B _)]; exact he.symm]
  simp only [exterior, Matrix.mulVec,dotProduct,Finset.sum_mul,Finset.mul_sum, ← sum_sub_distrib]
  conv_rhs => rw [sum_comm]
  -- swap dummy indices in second term? expressions A2_i A1_j yes
  apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; dsimp only [B]; ring

def basisVec (i : n) : n → ℂ := Pi.single i 1
lemma exterior_basis (i : Idx n) : exterior (basisVec i.val.1) (basisVec i.val.2) = Pi.single i 1 := by
  funext j; have hz : j.val ≠ i.val.swap := fun he => (not_lt_of_ge i.property.le) (by
    have hh := j.property; rw [he] at hh; exact hh)
  unfold exterior
  have he : basisVec i.val.1 j.val.2 * basisVec i.val.2 j.val.1=(0:ℂ) := by
    by_cases h:j.val.2=i.val.1
    · have hh : j.val.1 ≠ i.val.2 := fun e => hz (Prod.ext e h); simp [basisVec,Pi.single_apply,hh]
    simp [basisVec,Pi.single_apply,h]
  rw [he,sub_zero]; by_cases hj:j=i
  · simp [hj,basisVec]
  by_cases h:j.val.1=i.val.1
  · have hh : j.val.2 ≠ i.val.2 := fun e => hj (Subtype.ext (Prod.ext h e))
    simp [basisVec,Pi.single_apply,hh,hj]
  simp [basisVec,Pi.single_apply,h,hj]
lemma row_expand (A : Op n) (i : n) (v : n→ℂ) : (A.updateRow i v).det = ∑ j, v j*(A.updateRow i (basisVec j)).det := by
  let D : (n→ℂ) →ₗ[ℂ] ℂ :=
    { toFun w := (A.updateRow i w).det, map_add' := fun x y => Matrix.det_updateRow_add A i x y,
      map_smul' := fun x y => Matrix.det_updateRow_smul A i x y }
  change D v = ∑ j, v j * D (basisVec j)
  conv_lhs => rw [show v=∑ j:n, v j • basisVec j by ext x; simp [basisVec,Pi.single_apply]]
  simp
lemma rows_swap (A : Op n) {i j:n} (h : i≠j) (x y : n→ℂ) : ((A.updateRow i y).updateRow j x).det =
    -((A.updateRow i x).updateRow j y).det := by
  let M := (A.updateRow i x).updateRow j y
  rw [show (A.updateRow i y).updateRow j x = M.submatrix (Equiv.swap i j) id by
    apply Matrix.ext; intro l k; by_cases e:l=i
    · subst l; simp [M,Matrix.updateRow_ne h]
    by_cases f:l=j
    · subst l; simp [M, Matrix.updateRow_ne h]
    rw [Matrix.updateRow_ne f,Matrix.updateRow_ne e,Matrix.submatrix_apply,Equiv.swap_apply_of_ne_of_ne e f]
    dsimp only [M,id_eq]; rw [Matrix.updateRow_ne f, Matrix.updateRow_ne e]]
  rw [Matrix.det_permute,Equiv.Perm.sign_swap h]; simp only [Units.val_neg, Int.cast_neg,Units.val_one,Int.cast_one, neg_one_mul]; rfl
lemma twoRow (A : Op n) {i j:n} (h : i≠j) (x y : n→ℂ) : ((A.updateRow i x).updateRow j y).det =
    ∑ p:Idx n, exterior x y p * ((A.updateRow i (basisVec p.val.1)).updateRow j (basisVec p.val.2)).det := by
  let B := fun p:n×n => ((A.updateRow i (basisVec p.1)).updateRow j (basisVec p.2)).det
  have hb := alternSum B (fun _ => rows_swap _ h _ _) (fun _ => Matrix.det_zero_of_row_eq h
    (by rw [Matrix.updateRow_ne h,Matrix.updateRow_self, Matrix.updateRow_self])) x y
  rw [A.updateRow_comm h,row_expand, ← hb]; apply sum_congr rfl; intro k _
  rw [A.updateRow_comm (Ne.symm h), row_expand, mul_sum]; apply sum_congr rfl; intro l _; unfold B; rw [mul_assoc]
end YM.CF.ExTwo

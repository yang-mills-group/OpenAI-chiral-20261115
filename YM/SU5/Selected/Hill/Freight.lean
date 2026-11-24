import YM.SU5.Selected.Hill.Ice
/-! Diagonals (local price assumption upper); full periodic curl. -/
set_option autoImplicit false
noncomputable section
namespace YM.Hill.Calculus
open Function Filter Finset Lattice Tree Wilson RG Pressure Exterior Work.F03 Precision MeasureTheory Chene Trunk FreeResolvent Matrix Chene.Tail Melody SectorNext.Vacuum.FlatTree
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius MatrixOrder Matrix InnerProductSpace Kronecker
variable {G:Gauge}{n:Side}{T:Clip}(H:Bed){I:Type*}[Fintype I][DecidableEq I]
abbrev dollar(A:ℝ):= |A| *(16*(Fintype.card PlaqAxes:ℝ))+4
lemma tally (v: EdgeT n→ℝ)(p:Axis)(x:Site n)(q: PlaqAxes): song (x,q) v^2 ≤ 4*(v (x+step q.val.1,q.val.2)^2+v (x,q.val.2)^2+v (x+step q.val.2,q.val.1)^2+v (x,q.val.1)^2):=by
 have he(x y w z:ℝ) : (x-y-(w-z))^2 ≤ 4*(x^2+y^2+w^2+z^2):=by nlinarith only [sq_nonneg (x+y),sq_nonneg (w+z),sq_nonneg (x-y+w-z)]
 exact he ..
lemma axis_price (v: EdgeT n→ℝ)(p:Axis)(x:Site n): ∑ y:Site n, v (y+x,p)^2 ≤ v ⬝ᵥ v:=by
 let f:=fun y:Site n=> (y+x,p); have hf:Injective f:= fun j k w=> add_right_cancel (congrArg Prod.fst w)
 apply le_trans (FreeResolvent.Cost.sum_comp_le (f:=f) hf (fun i=> v i^2) (fun i=>sq_nonneg _)); exact le_of_eq (by simp only [sq,dotProduct]) -- tune
lemma curl_budget (v: EdgeT n→ℝ): (curl ℝ n*ᵥ v) ⬝ᵥ (curl ℝ n*ᵥ v) ≤ 16*(Fintype.card PlaqAxes:ℝ)*dotProduct v v:=by
 let V:=dotProduct v v; rw [dotProduct,Fintype.sum_prod_type,sum_comm]; simp_rw [curl_applyZ,←sq]; refine le_trans (sum_le_sum fun i _=> (show ∑ x:Site n,song (x,i) v^2 ≤16*V from ?_)) (le_of_eq ?_)
 · refine (sum_le_sum (fun x _=> tally v 0 x i)).trans ?_; rw [← mul_sum,sum_add_distrib,sum_add_distrib,sum_add_distrib]; have he(p):∑ x:Site n,v (x,p)^2 ≤ V:=by simpa using axis_price v p 0
   linarith only [he i.val.1,he i.val.2, axis_price v i.val.1 (step i.val.2), axis_price v i.val.2 (step i.val.1)]
 rw [sum_const,card_univ,nsmul_eq_mul]; unfold V; ring
lemma knot (j:EdgeT n)(p:Axis) : let k:=(pin ℝ n*ᵥ Pi.single j 1) p; k=0∨k=1:=by
 intro k; unfold k; rw [pin_apply]; by_cases v:∃ x:Per n,(lineK n p x,p)=j
 · right; obtain ⟨x,e⟩:= v; subst j; rw [sum_eq_single x,Pi.single_eq_same]; intro b _ u; rw [Pi.single_eq_of_ne]; exact fun h=> u ((by simpa [lineK] using congrFun (congrArg Prod.fst h) p)); simp
 left; exact sum_eq_zero fun x _=> Pi.single_eq_of_ne (fun h=>v ⟨x,h⟩) _
lemma dollar_use (u A:ℝ)(t:Floor H T n u A)(p:EdgeT n) : canopy n H p p ≤ dollar A:=by
 let M:=(H.metric.acts n); let v:EdgeT n→ℝ:=(Pi.single p (1:ℝ)); let W:=curl ℝ n*ᵥv; let Q:=pin ℝ n*ᵥv
 have hp: v ⬝ᵥ v=1:=by simp [v]; -- tune
 have he: canopy n H p p=W ⬝ᵥ M.submatrix (petals n) (petals n) *ᵥ W + Q ⬝ᵥ Q:=by
    unfold W Q; conv_lhs=> rw [show canopy n H p p=v ⬝ᵥ ((canopy n H)*ᵥ v) from (by simp [v])]
    rw [canopy,←flat_t,add_mulVec, dotProduct_add,←mulVec_mulVec,←mulVec_mulVec,←mulVec_mulVec,dotProduct_transpose_mulVec,dotProduct_transpose_mulVec]
    exact congrArg (· + _) (dotProduct_comm _ _)
 let Y:=W∘(petals n).symm
 have h0:W ⬝ᵥ W= Y ⬝ᵥ Y:=Equiv.sum_comp (petals n).symm (fun i=>W i*W i) |>.symm
 have h1:W ⬝ᵥ M.submatrix (petals n) (petals n) *ᵥ W= Y ⬝ᵥ (M*ᵥY):=by rw [submatrix_mulVec_equiv]; unfold Y; unfold dotProduct; rw [← Equiv.sum_comp (petals n) (fun i=> _*_)]; simp only [Function.comp_apply,Equiv.symm_apply_apply]
 have hX:0≤ W ⬝ᵥ W:=normSum_nn _
 have h2:= (t.uniform.1 Y).2; rw [←h0,← h1] at h2
 have hx:=curl_budget v; rw [hp,mul_one] at hx; rw [he]
 apply add_le_add (h2.trans ((mul_le_mul (le_abs_self A) hx hX (abs_nonneg A))))
 exact (sum_le_sum (g:=fun _=> (1:ℝ)) (fun i _=> by change Q i * Q i ≤1; obtain h|h:= knot (n:=n) p i<;> change Q i= _ at h<;> norm_num [h])).trans_eq (by rw [sum_const,card_univ,Fintype.card_fin]; norm_num) -- tune
lemma dollar_pass (f:I→EdgeT n)(u A:ℝ)(t:Floor H T n u A)(i:Pens G I) : cred f G H i i ≤ dollar A:=by
 simpa [cred,story] using dollar_use H _ _ t (f i.1)
end YM.Hill.Calculus
#print axioms YM.Hill.Calculus.dollar_pass

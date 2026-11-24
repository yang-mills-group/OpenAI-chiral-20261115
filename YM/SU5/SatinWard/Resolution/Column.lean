import Mathlib
/-! Shared column bookkeeping on a finite physical label menu.
All norms sup to keep a single constant/per-row, factors for layout arity appear elsewhere.
This file contains no physical estimates. -/
set_option autoImplicit false
set_option linter.flexible false
noncomputable section
namespace YM.CF.QuadClock.ShapeLab
open Function Filter Finset
open scoped Topology BigOperators
variable {ι J H:Type*}
abbrev Coords (ι:Type*):=ι→ℝ
variable [Fintype ι]
abbrev leg [DecidableEq ι](i:ι) : Coords ι:= Pi.single i 1

section
variable [AddCommGroup H][Module ℝ H]
noncomputable def columns (M:ι→H) : Coords ι→ₗ[ℝ] H where
 toFun x := ∑ i:ι,x i • M i
 map_add' x y:= by simp only [Pi.add_apply,add_smul,sum_add_distrib]
 map_smul' r x:=by simp only [Pi.smul_apply,smul_eq_mul,mul_smul,smul_sum]; rfl -- tune
@[simp] lemma columns_one [DecidableEq ι](M:ι→H)(i:ι):columns M (leg i)= M i:=by
 change (∑ j:ι, leg i j • M j) = _; rw [sum_eq_single i]; · simp [leg]
 · intro j _ v; simp [leg,v]
 simp
lemma cols_apply (M:ι→H)(x:Coords ι): columns M x= ∑ i:ι,x i • M i:=rfl
lemma columns_map (M:Coords ι→ₗ[ℝ] H) [DecidableEq ι]: columns (fun i=>M (leg i))= M := by
 apply LinearMap.ext; intro v; rw [cols_apply]; simp_rw [←M.map_smul]; rw [←map_sum]; congr 1; funext j; rw [Finset.sum_apply,sum_eq_single j] <;> simp_all [leg]
end
@[simp] lemma leg_norm [DecidableEq ι](i:ι): ‖leg i‖=1:=by
 -- import
 refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun j=>?_) ?_
 · by_cases t:j=i <;> simp [leg,t]
 exact (norm_le_pi_norm (leg i) i).trans' (by simp [leg])

section
variable [SeminormedAddCommGroup H][NormedSpace ℝ H]
lemma columns_price (F:ι→H)(x:Coords ι)(a:ℝ)(p:∀ i,‖F i‖≤ a): ‖columns F x‖ ≤ (Fintype.card ι:ℝ)* (a* ‖x‖):=by
 rw [cols_apply]; refine le_trans (norm_sum_le ..) ?_
 refine le_trans (b:= ∑ i:ι,a*‖x‖) (sum_le_sum fun i _=>?_) (by simp)
 rw [norm_smul,mul_comm a]; exact mul_le_mul (norm_le_pi_norm x i) (p i) (norm_nonneg _) (norm_nonneg _)
lemma columns_le_of_tips [DecidableEq ι](F:Coords ι→ₗ[ℝ] H)(x:Coords ι)(a:ℝ)(p:∀ i,‖F (leg i)‖≤a) : ‖F x‖ ≤ ((Fintype.card ι:ℝ)*a)*‖x‖:=by
 rw [←columns_map F,mul_assoc]; apply columns_price; exact p
end

variable [DecidableEq ι]
lemma diagonal_eval (z x:Coords ι)(i:ι): columns (fun i=> z i • leg i) x i = z i * x i:=by
 rw [cols_apply,Finset.sum_apply,sum_eq_single i]; · simp [leg,mul_comm]
 · intro j _ v; simp [leg,v.symm]
 simp
lemma inventory_neq (F:ι→ Coords ι)(z:Coords ι)(ε t:ℝ)(p:∀ i,‖F i-z i • leg i‖≤ε) (k:∀ i,t≤|z i|) (u:(Fintype.card ι:ℝ)*ε≤t/2) (h:0<t):
 ∃ A:Coords ι ≃ₗ[ℝ] Coords ι,
     (A : Coords ι →ₗ[ℝ] Coords ι)=columns F∧ ∀ x:Coords ι, ‖A.symm x‖ ≤ (2/t)* ‖x‖ := by
 let Q:=columns F; let G : Coords ι →ₗ[ℝ] Coords ι:= columns (fun i=>z i • leg i)
 have he (x:Coords ι) : ‖(Q-G) x‖ ≤ t/2*‖x‖ := (columns_le_of_tips _ x _ (show ∀ i,‖(Q-G) (leg i)‖≤ ε from fun i=>by simpa only [LinearMap.sub_apply,G,Q,columns_one] using p i)).trans (mul_le_mul_of_nonneg_right u (norm_nonneg _)) -- parser
 have hp (x:Coords ι): ‖x‖* t ≤ ‖G x‖:=by
    refine (le_div_iff₀ h).mp ((pi_norm_le_iff_of_nonneg (by positivity:0≤‖G x‖/t)).2 ?_); intro i
    apply (le_div_iff₀ h).2; unfold G; refine ((norm_le_pi_norm (columns (fun i=> z i • leg i) x) i)).trans' ?_; rw [diagonal_eval,norm_mul,mul_comm]; exact mul_le_mul_of_nonneg_right (k i) (norm_nonneg _)
 have hx(x:Coords ι): t/2*‖x‖ ≤ ‖Q x‖:= by
    have hw:‖G x‖-‖Q x‖≤ t/2*‖x‖:= (norm_sub_norm_le ..).trans ((norm_sub_rev (G x) (Q x)).le.trans (he x))
    linarith only [hp x,hw]
 have hq:Injective Q:=LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (fun x v=>by
    apply norm_le_zero_iff.mp -- tune! norm_eq_zero.mpr vs
    have w:=hx x; rw [v,norm_zero] at w; exact (nonpos_of_mul_nonpos_right w (half_pos h))))
 let A:=LinearEquiv.ofBijective Q ⟨hq,LinearMap.surjective_of_injective hq⟩
 refine ⟨A,rfl,fun x=>?_⟩; have hv:= hx (A.symm x); change t/2 * _≤ ‖A (A.symm x)‖ at hv; rw [A.apply_symm_apply] at hv
 refine (mul_le_mul_of_nonneg_left hv (show 0≤ 2/t by positivity)).trans' ?_; rw [← mul_assoc,show 2/t*(t/2)=1 by field_simp,one_mul]
end YM.CF.QuadClock.ShapeLab

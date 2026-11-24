import YM.CF.BPress.Scale

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Retinue

open Filter BPress
open scoped Topology

/-- shrinking factor. -/
def bit (n:ℕ)(x:ℝ):ℝ:=(lscale x ^ n)⁻¹
variable (f:ℕ→ℝ)(h:∀n:ℕ,(n:ℝ)≤f n)
lemma whistle (h:∀n:ℕ,(n:ℝ)≤f n):Tendsto f atTop atTop:= tendsto_atTop_mono h tendsto_natCast_atTop_atTop

/-- If earnings can use any NPL factor, a poly-log divisor suffices. -/
theorem bridle (A:ℝ→ℝ→Prop)
   (p:∀v:ℝ→ℝ,NPL v → ∀ᶠ x in atTop,A x (v x)):
  ∃ n:ℕ, ∀ᶠ x in atTop, A x (bit n x):=by
 by_contra! q
 have hy:∀ n:ℕ,∃ y:ℝ,(n:ℝ) ≤ y∧¬ A y (bit n y):= fun n=> ((eventually_ge_atTop (n:ℝ)).and_frequently (q n)).exists
 choose f u w using hy

 classical
 let j(y:ℝ)(i:y∈ Set.range f):ℕ:=i.choose
 let v (y:ℝ):ℝ:= if i:y∈Set.range f then bit (j y i) y else 0
 have t:NPL v:=by
   constructor
   intro k
   let S:=Finset.range (k+1)
   obtain ⟨b,hb⟩:=((S.image f).finite_toSet).bddAbove
   apply squeeze_zero' _ _
     (tendsto_inv_atTop_zero.comp lscale_late)
   · filter_upwards with y; have :0<lscale y:=zero_lt_one.trans_le (lscale_one _)
     unfold v bit; split <;> positivity
   filter_upwards [eventually_gt_atTop b] with y ty
   unfold v; split; swap; · rw [mul_zero]; exact inv_nonneg.mpr (zero_le_one.trans (lscale_one y))
   rename_i i
   unfold bit
   have e: k+1 ≤ j y i := le_of_not_gt fun t=> not_le_of_gt ty (hb (by
      show y∈ S.image f
      rw [←i.choose_spec]
      exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr t)))
   have h:=pow_le_pow_right₀ (lscale_one y) e; rw [pow_succ] at h
   have yt:0<lscale y:=zero_lt_one.trans_le (lscale_one _)
   change _*_ ≤ (lscale y)⁻¹
   rw [← div_eq_mul_inv, div_le_iff₀ (by positivity),inv_mul_eq_div,le_div_iff₀ yt]
   exact h
 obtain ⟨r,g⟩:=((whistle f u).eventually (p v t)).exists
 let i : f r∈Set.range f:=⟨_,rfl⟩
 rw [show v (f r)= _ from dif_pos i] at g
 exact w i.choose (i.choose_spec.symm ▸ g)

end YM.CF.Merino.Retinue

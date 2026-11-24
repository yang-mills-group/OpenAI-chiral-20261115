import Mathlib.Analysis.Complex.HasPrimitives
/-!
# Morera tool for BORDER of Wick cylinders
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Lens
open Function Set Filter Complex MeasureTheory
open scoped Topology Interval
variable {U:Set ℂ}{f:ℂ→ℂ}{t:ℝ}
  (H:∀ z∈U,z.re≠t→DifferentiableAt ℂ f z)(R:ContinuousOn f U)
include H R
local notation "Θ" => wedgeIntegral
private lemma seam_side (z w:ℂ)(p:Rectangle z w⊆ U)(h:z.re≤ w.re)(e:w.re≤t ∨ t≤z.re): Θ z w f+Θ w z f=0:=by
 rw [wedgeIntegral_add_wedgeIntegral_eq]; apply integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w (R.mono p)
 intro x s; have hr : z.re<x.re ∧ x.re<w.re := by simpa only [min_eq_left h,max_eq_right h,mem_Ioo] using (show x.re∈ Set.Ioo _ _ from s.1)
 have he: x∈ Rectangle z w := ⟨Ioo_subset_Icc_self s.1,Ioo_subset_Icc_self s.2⟩; apply (H x (p he) ?_).differentiableWithinAt
 rcases e with k|l; exact (hr.2.trans_le k).ne; exact (l.trans_lt hr.1).ne'
private lemma lineAdd {z w:ℂ}(p:Rectangle z w⊆ U)(h:z.re≤t)(k:t≤w.re) (a:ℝ)(e: a∈ [[z.im,w.im]]) :
    (∫ x:ℝ in z.re..t, f (x + a*I)) + (∫ x:ℝ in t..w.re, f (x + a*I)) = ∫ x:ℝ in z.re..w.re, f (x + a*I) :=by
 let g(x:ℝ):ℂ:= (x:ℂ)+a*I
 have ht:ContinuousOn (fun x:ℝ=>f (g x)) (Icc z.re w.re):= R.comp (show ContinuousOn g _ from (show Continuous g by unfold g; fun_prop).continuousOn) (fun x b => p (show g x ∈ Rectangle z w from (by rw [Rectangle,uIcc_of_le (h.trans k),mem_reProdIm]; simpa [g] using And.intro b e)))
 apply intervalIntegral.integral_add_adjacent_intervals
 · apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le h]; exact ht.mono (Icc_subset_Icc_right k)
 apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le k]; exact ht.mono (Icc_subset_Icc_left h)
private lemma seam_bottom (z w:ℂ)(p:Rectangle z w⊆ U)(h:z.re≤ w.re): Θ z w f+Θ w z f=0:=by
 by_cases a:t<z.re; exact seam_side H R z w p h (Or.inr a.le)
 by_cases b:w.re<t; exact seam_side H R z w p h (Or.inl b.le)
 let x:ℂ:= ⟨t,w.im⟩; let y:ℂ:=⟨t,z.im⟩; have hx:x.re=t:=rfl; have hy:y.re=t:=rfl
 let h₁:= le_of_not_gt a; let h₂:= le_of_not_gt b
 have u:=seam_side H R z x ?_ h₁ (Or.inl hx.le); swap
 · apply subset_trans _ p; unfold Rectangle; rw [uIcc_of_le h, hx,uIcc_of_le h₁]; exact inter_subset_inter_left _ (preimage_mono (Icc_subset_Icc_right h₂)) -- tune
 have w':=seam_side H R y w ?_ h₂ (Or.inr hy.ge); swap
 · apply subset_trans _ p; unfold Rectangle; rw [uIcc_of_le h, hy, uIcc_of_le h₂]; exact inter_subset_inter_left _ (preimage_mono (Icc_subset_Icc_left h₁))
 rw [wedgeIntegral_add_wedgeIntegral_eq] at u w' ⊢
 simp only [x,y] at u w'
 rw [← lineAdd (t:=t) H R p h₁ h₂ z.im left_mem_uIcc, ← lineAdd H R p h₁ h₂ w.im right_mem_uIcc] -- include H unused
 rw [← add_zero (0:ℂ)] -- add_zero occurrence issues
 nth_rw 1 [←u]; rw [←w']
 abel
lemma seam_cement (v:IsOpen U) : DifferentiableOn ℂ f U:=by
 refine (isConservativeOn_and_continuousOn_iff_isDifferentiableOn v).mp ⟨?_,R⟩
 intro z w p; rw [← add_eq_zero_iff_eq_neg]; rcases le_total z.re w.re with x|y
 · exact seam_bottom H R z w p x
 rw [add_comm]; apply seam_bottom H R w z _ y; unfold Rectangle; rwa [uIcc_comm w.re,uIcc_comm w.im]
end YM.Lens

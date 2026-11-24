import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Uniform radius estimates used on the fixed charts. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof
open Function Filter Metric Set
open scoped Topology ContDiff NNReal InnerProductSpace
variable {E D F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
  {f : E → D} {a : E}

lemma chargedLip (h : ContDiffAt ℝ ω f a) : ∃ C ε : ℝ,0<C ∧ 0<ε ∧ ∀ x∈closedBall a ε,
    ∀ y∈closedBall a ε, ‖f x-f y‖≤C*‖x-y‖ := by
 obtain ⟨K,T,hT,H⟩ := (h.of_le (show 1≤ ω by norm_cast)).exists_lipschitzOnWith -- order tune
 obtain ⟨r,hr,hk⟩ := Metric.mem_nhds_iff.mp hT
 refine ⟨K+1,r/2,by positivity,by positivity,fun x hx y hy =>?_⟩
 have hs : closedBall a (r/2) ⊆ T := (closedBall_subset_ball (by linarith)).trans hk
 exact (lipschitzOnWith_iff_norm_sub_le.mp H (hs hx) (hs hy)).trans (mul_le_mul_of_nonneg_right (by simp) (norm_nonneg _))

lemma quadratic (h : ContDiffAt ℝ ω f a) : ∃ C ε : ℝ,0<C ∧ 0<ε ∧ ∀ (r : ℝ), r≤ε →
    ∀ x ∈ closedBall a r,∀ y ∈ closedBall a r, ‖f x - f y - fderiv ℝ f a (x-y)‖ ≤ C*r*‖x-y‖ := by
 obtain ⟨C,ε,hC,he,H⟩:= chargedLip (f:=fderiv ℝ f) (h.fderiv_right (by simp))
 have hh : ∀ᶠ x in 𝓝 a,DifferentiableAt ℝ f x := (h.eventually (by simp)).mono fun _ u => u.differentiableAt (by simp)
 obtain ⟨r,hr,hv⟩:= Metric.mem_nhds_iff.mp hh
 refine ⟨C,min ε (r/2),hC,lt_min he (by positivity), fun u hu x hx y hy => ?_⟩
 have hl := hu.trans (min_le_left ..)
 have hm : closedBall a u ⊆ ball a r := closedBall_subset_ball ((hu.trans (min_le_right ..)).trans_lt (by linarith))
 refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f':= fderiv ℝ f) (fun x hx=> (show DifferentiableAt ℝ f x from hv (hm hx)).hasFDerivAt.hasFDerivWithinAt) (fun z hz=> ?_) (convex_closedBall a u) hy hx
 exact (H z (closedBall_subset_closedBall hl hz) a (mem_closedBall_self he.le)).trans (mul_le_mul_of_nonneg_left (by simpa [mem_closedBall,dist_eq_norm] using hz) hC.le)

lemma ImmBound [FiniteDimensional ℝ E] {L : E→L[ℝ] D} (hin : Injective L) : ∃ c : ℝ,0<c∧∀ x, c*‖x‖ ≤ ‖L x‖ := by
 obtain ⟨K,hK,H⟩:= LinearMap.exists_antilipschitzWith L.toLinearMap (LinearMap.ker_eq_bot.mpr hin)
 refine ⟨(K:ℝ)⁻¹,by exact inv_pos.mpr (by exact_mod_cast hK),fun x=>?_⟩
 rw [inv_mul_le_iff₀ (by exact_mod_cast hK : 0<(K:ℝ))]; simpa using H.le_mul_dist x 0

lemma ImmPrice [FiniteDimensional ℝ E] (h : ContDiffAt ℝ ω f a) (hin : Injective (fderiv ℝ f a)) :
    ∃ c ε : ℝ, 0<c ∧ 0<ε ∧ ∀ x∈closedBall a ε,c*‖x-a‖ ≤ ‖f x-f a‖ := by
 obtain ⟨c,hc,hp⟩:=ImmBound hin
 obtain ⟨C,δ,hC,hδ,hq⟩:= quadratic h
 let u := min δ (c/2/C); have hu : 0<u := lt_min hδ (by positivity)
 refine ⟨c/2,u,by positivity,hu,fun x hx=>?_⟩
 have hv := hq u (min_le_left ..) x hx a (mem_closedBall_self hu.le)
 have hd : C*u*‖x-a‖≤ c/2*‖x-a‖ := by gcongr; rw [mul_comm]; exact (le_div_iff₀ hC).mp (min_le_right ..)
 have hk:= norm_le_norm_sub_add (fderiv ℝ f a (x-a)) (f x-f a); rw [norm_sub_rev] at hk; linarith [hp (x-a)]

/-- At a minimum the residual is perpendicular to a whole patch's tangent. Gives
local uniqueness against minimizers in that patch, with uniform allowance for the datum's
distance to the minimizing point. -/
theorem ImmNormal [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] {f : E→F}
    (h : ContDiffAt ℝ ω f a) (hin : Injective (fderiv ℝ f a)) :
    ∃ b δ : ℝ,0<b ∧ 0<δ ∧ ∀ x∈ball a b,∀ y : F, ‖y-f a‖ ≤ δ → (∀ x, ‖y-f a‖ ≤ ‖y-f x‖) →
            ‖y-f x‖ ≤ ‖y-f a‖ → x=a := by
 obtain ⟨c,b,hc,hb,hp⟩:= ImmPrice h hin
 obtain ⟨C,d,hC,hd,hq⟩:= quadratic h
 let δ := c^2/(4*C); have hδ:0<δ:=by dsimp [δ]; positivity
 refine ⟨min b d,δ, lt_min hb hd,hδ, fun x hx y hy he hz =>?_⟩
 let L:=fderiv ℝ f a
 have hn (w : E) : ⟪y-f a,L w⟫_ℝ=0:=by
   have H : IsLocalMin (fun t : ℝ => ‖f (a+t • w)-y‖^2) 0:=Eventually.of_forall fun t => by simp only [zero_smul,add_zero, norm_sub_rev _ y]; exact pow_le_pow_left₀ (norm_nonneg _) (he _) _ -- tune
   have hh : HasFDerivAt f L (a+(0:ℝ) • w):=by simpa using (h.differentiableAt (by simp)).hasFDerivAt;
   have hj : HasDerivAt (fun t : ℝ => a+t • w) w 0 := by simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const w).const_add a
   have hs : HasDerivAt (fun t : ℝ => f (a+t • w)) (L w) 0 := hh.comp_hasDerivAt _ hj
   have hk:= H.hasDerivAt_eq_zero (hs.sub_const y).norm_sq
   simp only [Function.comp_apply, zero_smul, add_zero] at hk -- deal
   rw [← neg_sub,inner_neg_left]; simpa using hk
 let w:= x-a; let M:=f x-f a; let R:=y-f a
 have hv : ‖R-M‖^2≤‖R‖^2:=pow_le_pow_left₀ (norm_nonneg _) (by simpa [M,R] using hz) _
 rw [norm_sub_sq_real] at hv
 have hh : ⟪R,M⟫_ℝ ≤ δ*(C*‖w‖*‖w‖) := calc
   _ = ⟪R,M-L w⟫_ℝ := by rw [inner_sub_right (𝕜:=ℝ) R M (L w),show ⟪R,L w⟫_ℝ=0 from hn w,sub_zero]
   _ ≤ ‖R‖*‖M-L w‖ := real_inner_le_norm ..
   _ ≤ _ := mul_le_mul hy (by
       have hw : ‖x-a‖≤ d := by rw [mem_ball,dist_eq_norm] at hx; exact hx.le.trans (min_le_right ..)
       exact hq ‖x-a‖ hw _ (by simp [mem_closedBall,dist_eq_norm]) _ (mem_closedBall_self (norm_nonneg _))) (norm_nonneg _) hδ.le
 have ht : c*‖w‖ ≤ ‖M‖:= hp x (ball_subset_closedBall ((ball_subset_ball (min_le_left ..)) hx))
 have hl := pow_le_pow_left₀ (mul_nonneg hc.le (norm_nonneg w)) ht 2
 have hi : δ*(C*‖w‖*‖w‖)=(c*‖w‖)^2/4 := by dsimp only [δ]; field_simp
 rw [hi] at hh
 by_contra hf
 have hw : 0<‖w‖:= norm_pos_iff.mpr (sub_ne_zero.mpr hf)
 linarith [sq_pos_of_pos (mul_pos hc hw)]
end YM.CF.BProof

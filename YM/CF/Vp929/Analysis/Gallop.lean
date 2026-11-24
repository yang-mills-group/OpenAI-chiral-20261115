import YM.CF.Vp929.Analysis.Slit
import Mathlib.Analysis.Complex.RemovableSingularity
set_option autoImplicit false
noncomputable section
namespace YM.CF.VolumeRate
open Complex Metric Finset Filter Function
/- interpolation at n≤6 equally spaced real points x_i=i/8 for i<n. Iterated divided-
 difference form, B/R^n payment (Cauchy alternative). -/
private lemma norm_tick (n:ℕ): ‖(n:ℂ)/8‖ = (n:ℝ)/8:= by norm_num
lemma of_knots (n:ℕ){z:ℂ}(hn:n ≤ 6){f:ℂ→ℂ}{r b B:ℝ}(w:z∈ Metric.ball (0:ℂ) 1.5)(hb:0≤b)(hB:0≤ B)(hr:4 ≤ r) (u:DifferentiableOn ℂ f (closedBall 0 r))(p:∀ i:ℕ,i<n → ‖f ((i:ℂ)/8)‖≤b)(h:∀ z∈closedBall (0:ℂ) r,‖f z‖ ≤ B): ‖f z‖≤ 100^n*(b+B/r^n):= by
 induction n generalizing f b B with
 | zero => simpa using ((h z (closedBall_subset_closedBall (by linarith : (1.5:ℝ)≤r) (ball_subset_closedBall w))).trans (le_add_of_nonneg_left hb): ‖f z‖ ≤ b+B)
 | succ n ih=>
    let x:ℂ:=(n:ℂ)/8; have he:‖x‖≤1:=by
       unfold x; rw [norm_tick]; have : (n:ℝ)≤6:=by exact_mod_cast (show n ≤ 6 by omega)

       linarith

    have t:x∈ball (0:ℂ) r:=mem_ball_zero_iff.mpr (by linarith); let hx:= (p _ (Nat.lt_add_one n))
    let G:=dslope f x
    let V:=(4*B)/r; have hv:0≤ V:= div_nonneg (by positivity) (by linarith)
    have R:DifferentiableOn ℂ G (closedBall (0:ℂ) r):=(Complex.differentiableOn_dslope (closedBall_mem_nhds_of_mem t)).2 u
    have A(k): k<n→ (1/8:ℝ) ≤ ‖(k:ℂ)/8-x‖ := by
       intro k'; unfold x; rw [←sub_div,norm_div,← Complex.ofReal_natCast (n:=k),←Complex.ofReal_natCast (n:=n),← Complex.ofReal_sub,norm_real,Real.norm_eq_abs]; have ht:(k:ℝ)+1 ≤ n:= by exact_mod_cast k'
       rw [abs_of_nonpos (by linarith)]; norm_num; linarith
    have vk : ‖G z‖ ≤ 100^n*((16*b)+V/r^n):= ih (by omega) (by positivity) hv R (fun k tk=>?_) ?_
    · let U:=norm_add_le (f x) ((z-x)*G z); have e:f z=f x+(z-x)*G z:= Eq.symm ((by rw [show (z-x)*G z=f z-f x from sub_smul_dslope f x z]; abel)); rw [e]; rw [norm_mul] at U; refine U.trans (le_trans (add_le_add hx (mul_le_mul (((norm_sub_le z x).trans (add_le_add (mem_ball_zero_iff.mp w).le he)).trans (by norm_num:(1.5:ℝ)+1≤3)) vk (norm_nonneg _) (by norm_num))) ?_ ); have h:1≤ (100:ℝ)^n:= one_le_pow₀ (by norm_num); have h':0<r:=by linarith
      rw [show V/r^n= 4*(B/r^(n+1)) from by unfold V; rw [pow_succ]; ring, pow_succ (100:ℝ)]; nlinarith [show 0≤ B/r^(n+1) by positivity, mul_nonneg (sub_nonneg.mpr h) hb]
    · unfold G; have hh:=A k tk; have hu:0<‖(k:ℂ)/8-x‖:=by linarith
      rw [dslope_of_ne f (sub_ne_zero.mp (norm_pos_iff.mp hu)) , slope_def_module, norm_smul, norm_inv];
      apply (inv_mul_le_iff₀ hu).2; refine (norm_sub_le ..).trans (le_trans (add_le_add (p k (Nat.lt.step tk)) hx) ?_); nlinarith
    intro z u'; refine norm_le_of_forall_mem_frontier_norm_le isBounded_closedBall ⟨R,R.continuousOn.mono (by rw [isClosed_closedBall.closure_eq])⟩ ?_ (subset_closure u')
    intro k t'; rw [frontier_closedBall _ (by linarith :r≠0)] at t'; have hK:‖k‖=r:= by simpa only [mem_sphere,dist_zero_right] using t'
    have ht: r/2 ≤ ‖k-x‖:=by have hh:= norm_sub_norm_le k x; linarith
    have hu:0<‖k-x‖:= by linarith
    unfold G; rw [dslope_of_ne f (sub_ne_zero.mp (norm_pos_iff.mp hu)) , slope_def_module,norm_smul, norm_inv]
    refine (inv_mul_le_iff₀ hu).2 ((norm_sub_le ..).trans (le_trans (add_le_add (h _ (sphere_subset_closedBall t')) (h x (ball_subset_closedBall t))) ?_)); unfold V; rw [←mul_div_assoc, le_div_iff₀ (by linarith :0<r)]; nlinarith
end YM.CF.VolumeRate

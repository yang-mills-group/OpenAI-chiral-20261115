import YM.CF.Ember.Bud
set_option autoImplicit false
noncomputable section
namespace YM.CF.Ember
open Function Filter Lat Lattice Metric MeasureTheory Finset Stationary
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal
variable {N : Side}
structure SnowH (F: Gaia→ℝ) (r:ℝ):Prop where
 tilt(x: Gaia)(h:x≠0): ContDiffAt ℝ 1 F x
 hom(t:ℝ)(p:0<t)(x:Gaia): F (t • x)=F x/(t^4)
 fare{μ:ℝ}(h:0<μ)(e:μ≤1): cartWeight*(∫ x in orbShell μ,F x)=r*Real.log μ⁻¹
namespace SnowH
variable {F:Gaia→ℝ}{r:ℝ}(S:SnowH F r)
include S
lemma pay {μ:ℝ}(h:0<μ) : IntegrableOn F (orbShell μ) volume := by
 let s:= closedBall (0:Gaia) 1 \ ball 0 μ
 have hx : IsCompact s := (isCompact_closedBall _ _).diff isOpen_ball
 have he : ContinuousOn F s := fun x h'=> (S.tilt x (fun p=>h'.2 (p ▸ mem_ball_self h))).continuousAt.continuousWithinAt
 exact (he.integrableOn_compact hx).mono_set (by rw [shell_def]; exact Set.diff_subset_diff_right ball_subset_closedBall)
lemma chill : ∃ C:ℝ, 0<C ∧ ∀ p:Gaia,∀ h:0<‖p‖, ‖F p‖ ≤ C/‖p‖^4 ∧
     ∀ x:Gaia, ‖x-p‖≤ ‖p‖/2→ ‖F x-F p‖ ≤ C*‖x-p‖/‖p‖^5 :=by
 let s := closedBall (0:Gaia) 2 \ ball 0 (1/2)
 have hk : IsCompact s:= (isCompact_closedBall _ _).diff isOpen_ball
 have he (x) (h:x∈s):= S.tilt x (fun p=>h.2 (p ▸ mem_ball_self (by norm_num : (0:ℝ)<1/2)))
 let B := fun x=> ‖F x‖+‖fderiv ℝ F x‖
 obtain ⟨C,hC⟩:=hk.bddAbove_image (f:=B) (fun x h=> ((he x h).continuousAt.norm.add ((he x h).continuousAt_fderiv (by decide)).norm).continuousWithinAt)
 let A:=max C (1:ℝ)
 have ht(x)(h:x∈s): ‖F x‖≤A ∧ ‖fderiv ℝ F x‖≤A:=by
   have hxx : B x≤ A:= (hC ⟨x,h,rfl⟩).trans (le_max_left ..); exact ⟨(le_add_of_nonneg_right (norm_nonneg _)).trans hxx,(le_add_of_nonneg_left (norm_nonneg _)).trans hxx⟩
 refine ⟨A,lt_max_of_lt_right (by norm_num : (0:ℝ)<1),fun p hr=>?_⟩
 let r:=‖p‖; let P:=r⁻¹ • p; let K:=closedBall P (1/2)
 change 0<r at hr
 have hx(y:Gaia)(w):(‖y-w‖)≤ ‖y-w‖:=le_rfl
 have hp : ‖P‖=1:= by rw [show P=r⁻¹ • p from rfl,norm_smul,Real.norm_of_nonneg (by positivity)]; exact inv_mul_cancel₀ hr.ne'
 have hv : K⊆s:=by
    intro x h; have h' : ‖x-P‖≤1/2:=by simpa only [K,mem_closedBall,dist_eq_norm] using h
    have hk:= abs_le.mp ((abs_norm_sub_norm_le x P).trans h'); rw [hp] at hk
    change _∧_; simp only [mem_ball,mem_closedBall,dist_zero_right,not_lt]; constructor <;> linarith [hk.1,hk.2]
 have hy : P∈K:= mem_closedBall_self (by norm_num)
 have hz(x:Gaia): F x=F (r⁻¹ • x)/r^4:=by rw [S.hom _ (by positivity)]; field_simp
 constructor
 · nth_rw 1 [hz p]; rw [norm_div,Real.norm_of_nonneg (pow_nonneg hr.le 4)]; exact div_le_div_of_nonneg_right (ht P (hv hy)).1 (pow_nonneg hr.le 4)
 intro x hg; let z:=r⁻¹ • x
 have hf : ‖z-P‖=‖x-p‖/r:=by unfold z P; rw [← smul_sub,norm_smul,Real.norm_of_nonneg (by positivity),inv_mul_eq_div]
 have hl : z∈K:=by rw [show K=closedBall _ _ from rfl,mem_closedBall,dist_eq_norm,hf,div_le_iff₀ hr]; exact hg.trans_eq (by unfold r; ring)
 have hh:=Convex.norm_image_sub_le_of_norm_fderiv_le (fun x h=> (he x (hv h)).differentiableAt (by decide)) (fun x h=> (ht x (hv h)).2) (convex_closedBall ..) hy hl
 rw [hz x,hz p,← sub_div,norm_div,Real.norm_of_nonneg (pow_nonneg hr.le 4)]; rw [hf] at hh
 exact (div_le_div_of_nonneg_right hh (pow_nonneg hr.le _)).trans_eq (by unfold r; ring)
end SnowH

lemma peelH {μ:ℝ}(h:0<μ)(v:μ≤1): (∫ x : Gaia in orbShell μ,(‖x‖^5)⁻¹)=2*Real.pi^2*(μ⁻¹-1):=by
 rw [shell_turn μ h v fun x=>(x^5)⁻¹]; apply congr_arg _
 have hv:0 ∉ Set.uIcc μ 1:= by rw [Set.uIcc_of_le v]; exact fun p=> h.not_ge p.1
 rw [intervalIntegral.integral_congr (g:=fun x:ℝ=>x^(-2:ℤ)),integral_zpow (n:=(-2:ℤ)) (Or.inr ⟨by norm_num,hv⟩)]; norm_num; ring
 intro x hx; have h:=show x≠0 from fun p=>hv (p ▸ hx); field_simp
end YM.CF.Ember

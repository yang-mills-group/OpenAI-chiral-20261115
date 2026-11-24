import YM.CF.DPress.Analytic.Stead
/-! eq:gCbound; direct residue using conjugate pole outside contour. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.DPress.Analytic
open Function Set Filter Metric MeasureTheory Complex Real
open scoped Topology Classical ContDiff InnerProductSpace ComplexConjugate
variable {L R A:ℝ}{f:ℂ→ℂ}
private lemma century (u:1<R) {z:ℂ}(p:z∈ closedBall 0 R): (R:ℂ)^2-z ≠ 0:=sub_ne_zero.mpr (Ne.symm (fun e=> by subst z; rw [mem_closedBall_zero_iff,norm_pow,Complex.norm_real,Real.norm_of_nonneg (by linarith : 0≤R)] at p; nlinarith)) -- norm zero p.
private lemma visQ (H:ℂ→ℂ)(R:ℝ): circleAverage H 0 R=∫ x,H (φ R x)∂ωμ:=by unfold circleAverage ωμ; rw [integral_smul_measure,ENNReal.toReal_ofReal (by positivity :0≤ (2*Real.pi)⁻¹), intervalIntegral.integral_of_le (by positivity)]; rfl
private lemma fine (f:ℝ → ℂ)(p:Continuous f): Integrable f ωμ:= (p.intervalIntegrable .. |>.1).smul_measure ENNReal.ofReal_ne_top
private lemma west (t:1<R)(x:ℝ): let z:=φ R x; conj (tor R x)= z/((R:ℂ)^2-z) :=by
 let z:= φ R x; let v:= tor R x; have he : ‖z‖= R:= (norm_circleMap_zero R x).trans (abs_of_pos (by linarith : 0< R)); have hu:z*conj z=(R:ℂ)^2:=by rw [Complex.mul_conj,Complex.normSq_eq_norm_sq, ofReal_pow,he]; -- tune
 have hz:z≠0:= norm_pos_iff.mp (he.symm ▸ (show 0<R from by linarith)); have hv:conj z-1≠0:= by rw [← map_one (starRingEnd ℂ),← map_sub]; intro v; exact χ _ t _ (star_injective (show star (z-1)= star (0:ℂ) from v.trans (star_zero ℂ).symm)) -- tune
 intro z'; unfold tor; rw [map_inv₀,map_sub,map_one]; change (conj z-1)⁻¹=z/(_-z); field_simp [century t (show z∈Metric.closedBall 0 R from mem_closedBall_zero_iff.mpr he.le),hv]; simp_rw [← hu]; ring -- tune
lemma phaseD (h:DifferentiableOn ℂ f (ank L)): Disc L (fun x=> f x-conj (f x)) (f 1-f 0):=by
 let K:= Disc.ofDiff h; have hm (R:ℝ)(p:1<R)(k:R<L):Continuous (f ∘ φ R):= continuousOn_univ.mp (h.continuousOn.comp (φ_C R).continuousOn (fun i _=> β R L k (by linarith) i)); have he(R:ℝ)(p:1<R)(k:R<L): Integrable (fun x=> tor R x*conj (f (φ R x))) ωμ:= fine _ ((tor_C R p).mul (continuous_conj.comp (hm R p k))) -- name
 constructor; · intro R p k; simp_rw [mul_sub]; exact (K.χ R p k).sub (he R p k)
 intro R p k; let F(z:ℂ):= z/((R:ℂ)^2-z)*f z; have hp:DifferentiableOn ℂ F (closedBall 0 R):= (differentiableOn_id.div ((differentiableOn_const _).sub differentiableOn_id) (fun i v=> century p v)).mul (h.mono (closedBall_subset_ball k)); have hx : DiffContOnCl ℂ F (ank |R|):=by rw [abs_of_pos (by linarith : 0<R)]; exact ⟨hp.mono ball_subset_closedBall,hp.continuousOn.mono (closure_minimal ball_subset_closedBall isClosed_closedBall)⟩
 have hF:= hx.circleAverage (c:=0) (R:=R); rw [visQ] at hF; have hs : ∫ x, tor R x*conj (f (φ R x)) ∂ ωμ=0:=by
    apply star_injective; change conj _=conj 0; rw [map_zero,← integral_conj]; simp_rw [map_mul, conj_conj, show ∀ x, conj (tor R x)= (φ R x) / ((R:ℂ)^2 - (φ R x)) from fun x=> west p x]; change ∫ x, F (φ R x) ∂ ωμ=0; rw [hF]; simp [F]
 simp_rw [mul_sub]; rw [integral_sub (K.χ R p k) (he R p k),K.read R p k,hs,sub_zero]
private lemma lozenge(z:ℂ): ‖z-conj z‖ ≤ 2*|z.im|:=by rw [show z-conj z=((2*z.im:ℝ):ℂ)*I from Complex.ext (by simp) (by simp; ring), norm_mul,Complex.norm_I, mul_one, Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg zero_le_two] -- tune
open Finset
lemma stageD {I:Type*}(S:Finset I)(V:I→ℂ→ℂ)(v:∀ i∈S,DifferentiableOn ℂ (V i) (ank L))(w:I→ℝ)(t:∀ i∈ S,0≤w i)(p:∀ x∈ank L,(∑ i∈ S,w i*|(V i x).im|)≤A)(g:1<L): (∑ i∈S,w i*‖V i 1-V i 0‖)≤ 2*A/(L-1) :=by
 let z(i:I):= V i 1 - V i 0; let d(i:I):ℂ:= (‖z i‖:ℝ) / z i; let e(i:I):= (w i:ℂ)*d i; have he(i:I):‖d i‖≤1 ∧ d i*z i= (‖z i‖:ℝ):=by
    by_cases h:z i=0; unfold d; simp [h]; refine ⟨?_,by unfold d; field_simp⟩; unfold d; rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _),div_self (norm_ne_zero_iff.mpr h)]
 let F(i:I)(x:ℂ):= V i x - conj (V i x); let W:= ∑ i∈S,e i*z i; let y(x:ℂ):= ∑ i∈S,e i*F i x; have h:Disc L y W:= Disc.sum S _ _ (fun i p=>Disc.scale _ (phaseD (v _ p))); let C:= ∑ i∈S,w i*‖z i‖; have hv:W=(C:ℂ):=by unfold W e C; simp only [Complex.ofReal_sum,Complex.ofReal_mul]; apply sum_congr rfl; intro i v; rw [mul_assoc,(he i).2]
 rw [hv] at h; have hh:= h.value (a:=2*A) ?_ g; rw [Complex.norm_real, Real.norm_of_nonneg (sum_nonneg fun i g=>mul_nonneg (t i g) (norm_nonneg (z i)))] at hh; exact hh; intro x q; unfold y; apply (norm_sum_le ..).trans; refine (sum_le_sum (g:=fun i=> 2*(w i*|(V i x).im|)) (fun i q=> ?_)).trans ?_; · unfold e; rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (t i q)]; apply le_trans (mul_le_mul (mul_le_of_le_one_right (t i q) (he i).1) (lozenge (V i x)) (norm_nonneg _) (t i q)); exact (le_of_eq (by ring)) -- tune
 rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (p x q) zero_le_two
end YM.CF.DPress.Analytic

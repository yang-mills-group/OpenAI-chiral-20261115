import YM.SU5.FiniteGaugeData.ArchiveK.Elm
import Mathlib.Analysis.Fourier.Inversion
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
open Set MeasureTheory.Measure
open scoped FourierTransform
/- Fourier.E temporal Laplace. `μ E`. -/
section
variable {E:ℝ}(h:0<E)
def weave (E z:ℝ):ℂ:= Real.exp (-E*|z|)
abbrev whey(E u:ℝ):ℝ:=2/(E^2+u^2)
@[fun_prop] lemma weave_C : Continuous (weave E):=by unfold weave; fun_prop
include h
private lemma weave_Int : Integrable (weave E):=by
 let f:=weave E; have he:IntegrableOn f (Set.Ioi 0):= ((integrableOn_exp_mul_Ioi (neg_neg_of_pos h) 0).ofReal).congr (ae_restrict_of_forall_mem measurableSet_Ioi (fun x v=>by unfold f weave; rw [abs_of_pos (show 0<x from v)]; rfl)) -- syntax?
 rw [←integrableOn_univ,←Set.union_compl_self (Set.Ioi (0:ℝ))]; rw [Set.compl_Ioi]; apply he.union; apply ((integrableOn_exp_mul_Iic h 0).ofReal).congr (ae_restrict_of_forall_mem measurableSet_Iic fun x v=>?_); unfold f weave; rw [abs_of_nonpos v,neg_mul_neg]; rfl
#check Real.fourier_real_eq_integral_exp_smul
#check Real.fourierInv_eq
set_option quotPrecheck false
local notation "O"=> τ
@[fun_prop] lemma whey_C : Continuous (whey E):=by unfold whey; exact (Continuous.div₀ continuous_const (by fun_prop) (fun i=>by dsimp; positivity)) -- tune
lemma whey_I : Integrable (whey E):=by
 let F:=whey E; let Y:=Metric.closedBall (0:ℝ) 1; rw [←integrableOn_univ,←Set.union_compl_self Y]; apply ((whey_C h).continuousOn.integrableOn_compact (isCompact_closedBall _ _)).union; have he:= (show Integrable (fun u :ℝ => (1+‖u‖)^(-(2:ℝ))) from integrable_one_add_norm (by norm_num)); apply Integrable.mono' ((he.const_mul 8).integrableOn) ((whey_C h).aestronglyMeasurable) ?_
 filter_upwards [ae_restrict_mem (isClosed_closedBall.measurableSet.compl : MeasurableSet Yᶜ)] with u p; rw [Set.mem_compl_iff,mem_closedBall_zero_iff,not_le,Real.norm_eq_abs] at p; unfold whey; rw [Real.norm_of_nonneg (by positivity : 0 ≤ 2/(E^2+u^2))]; norm_num; rw [← div_eq_mul_inv]; rw [div_le_div_iff₀ (by positivity) (by positivity)]; have hy: (1+|u|)^2 ≤ (2*|u|)^2 := by gcongr; linarith only [p];
 rw [mul_pow, sq_abs] at hy; refine le_trans (mul_le_mul_of_nonneg_left hy (show (0:ℝ) ≤ 2 by norm_num)) ?_; calc 2*(2^2*u^2) ≤ 8*u^2:= le_of_eq (by ring)
                                                                          _ ≤ 8*(E^2+u^2):= mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg _)) (by norm_num)
lemma whey_B(u:ℝ) : 𝓕 (weave E) u= ((E*whey E (τ * u):ℝ):ℂ):=by
 let b:ℝ:=τ*u; let a:= (E:ℂ)+ Complex.I*b; let c:=(E:ℂ)-Complex.I*b; let A(x:ℝ):= Complex.exp (-a*x); let Cf(x:ℝ):=Complex.exp (c*x)
 have hp:-a.re<0:=by simp [a,h];
 have hv:0<c.re:=by simp [c,h];
 let f(x):=coastE (-b*x) * weave E x; have he : Integrable f:= (weave_Int h).norm.mono' (f:=f) (by unfold f; fun_prop) (Eventually.of_forall (fun x=>by unfold f; simp [norm_mul])) -- orientation
 have hA(x:ℝ)(y:0≤x):f x=A x:=by unfold f A weave coastE; rw [abs_of_nonneg y,ofReal_exp,←Complex.exp_add]; congr 1; unfold a; push_cast; ring
 have hC(x:ℝ)(y:x≤0):f x=Cf x:=by unfold f Cf weave coastE; rw [abs_of_nonpos y,ofReal_exp,← Complex.exp_add]; congr 1; unfold c; push_cast; ring
 have hm: 𝓕 (weave E) u=∫ x:ℝ,f x:=by rw [Real.fourier_real_eq_integral_exp_smul]; apply integral_congr_ae; filter_upwards with x; unfold f coastE; rw [smul_eq_mul]; unfold b τ; push_cast; ring_nf
 rw [hm,←integral_add_compl measurableSet_Ioi he,compl_Ioi] -- `s` inferred?
 let Z:=Set.Ioi (0:ℝ); rw [show ∫ x in Z,f x=∫ x in Z,A x from integral_congr_ae (ae_restrict_of_forall_mem measurableSet_Ioi fun x v=> hA x (show 0<x from v).le),show ∫ x:ℝ in Set.Iic 0,f x=∫ x in Set.Iic 0,Cf x from integral_congr_ae (ae_restrict_of_forall_mem measurableSet_Iic fun x v=> hC x v)] -- tune
 unfold A Cf; rw [integral_exp_mul_complex_Ioi (a := -a) (by rwa [Complex.neg_re]),integral_exp_mul_complex_Iic hv]; simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero]; have hxE: E^2+b^2≠0:= by positivity
 have hx: a*c= ((E^2+b^2:ℝ):ℂ):=by unfold a c; push_cast; ring_nf; simp
 unfold whey; change _=((E*(2/(E^2+b^2)):ℝ):ℂ); rw [ofReal_mul, ofReal_div, ofReal_ofNat, ←hx]; have hg:a≠0:= by intro g; rw [g,Complex.zero_re] at hp; linarith
 have hs:c≠0:=by intro h; rw [h, Complex.zero_re] at hv; linarith
 field_simp; unfold a c; ring
-- static Cf Fourier
lemma whet (X:ℝ): (∫ u:ℝ, coastE (X*u)*(whey E u:ℂ))=((τ/E:ℝ):ℂ)*weave E X:=by
 let H:= weave E; let W:= 𝓕 H; let q(u:ℝ):= ((E*whey E (τ*u):ℝ):ℂ); let V: W=q:=funext (whey_B h)
 have ht: Integrable W:= V ▸ ((((integrable_comp_mul_left_iff (whey E) tau_pos.ne').2 (whey_I h)).const_mul E).ofReal) -- tune
 let f(u:ℝ):= coastE (X*u)*(whey E u:ℂ); have hp:𝓕⁻ W X=(E:ℂ)*(∫ u:ℝ,f (τ*u)):=by
    rw [Real.fourierInv_eq_fourier_neg,Real.fourier_real_eq_integral_exp_smul,←integral_const_mul]; refine integral_congr_ae (Eventually.of_forall (fun i=>?_)); rw [V]; unfold q f coastE τ; push_cast; rw [smul_eq_mul]; ring_nf
 have he: 𝓕⁻ W X= weave E X:= (weave_Int h).fourierInv_fourier_eq ht weave_C.continuousAt; change (∫ u:ℝ,f u)=_; rw [←he,hp,MeasureTheory.Measure.integral_comp_mul_left f τ]; rw [Complex.real_smul,abs_of_nonneg (inv_nonneg.mpr tau_pos.le), ofReal_div, ofReal_inv]; have ht:E≠0:=h.ne'; have hx:τ≠0:= tau_pos.ne'; field_simp
end
#print axioms whet
end YM.CF.Window.ArchiveK

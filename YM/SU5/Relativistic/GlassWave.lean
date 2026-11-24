import YM.SU5.Relativistic.Cloudborn
import Mathlib.Analysis.Fourier.AddCircleMulti
/-! # Uniform approximation at exponential tariff. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Sleet
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Next.Free
open Laurent Bloch Fir Jill Ember Shore
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
local notation "I"=>Complex.I
local notation "Φ"=> Set.Icc (-π) π
local notation "T₀" => 2 * Real.pi
private instance f_positive: Fact (0 < 2*Real.pi):= ⟨by positivity⟩
def soundT (n:ℤ)(t:ℝ):= surge (-(n:ℝ)) t
lemma sound_norm (n:ℤ)(t:ℝ): ‖soundT n t‖=1:= surge_norm _ _
lemma sound_con (n:ℤ): Continuous (soundT n):=surge_cont.comp (continuous_const.prodMk continuous_id)
@[simp] lemma sound_neg (n:ℤ)(t:ℝ): soundT (-n) t= surge n t:=by simp [soundT]
@[simp] lemma surge0(t:ℝ):surge 0 t=1:=by simp [surge]
@[simp] lemma sound0 (t:ℝ): soundT 0 t=1:=by simp [soundT]
abbrev wrapT (n:ℤ)(f:ℝ→ℂ):ℂ:= (↑(T₀:ℝ):ℂ)⁻¹*pluse n f
open AddCircle
private lemma benchmark (n:ℤ)(t:ℝ): fourier (T:=2*π) n t = soundT (-n) t:=by
 rw [sound_neg,fourier_coe_apply, surge]; have he: (Real.pi:ℂ)≠0:=by exact_mod_cast Real.pi_pos.ne'
 push_cast; field_simp
private lemma otherBand : -π+2*π=π:= by ring
lemma buzz (f:ℝ→ℂ)(p:ContinuousOn f Φ)(q:f (-π)=f π)(h:Summable (fun n:ℤ=>wrapT n f))(t:ℝ)(w:t∈Set.Icc (-π) π) : HasSum (fun n:ℤ=> wrapT n f*soundT n t) (f t):=by
 let g:= AddCircle.liftIoc (2*Real.pi) (-π) f
 have hv:Continuous g:= liftIoc_continuous (by rwa [otherBand]) (by rwa [otherBand])
 let F : C(AddCircle (2*Real.pi),ℂ):=⟨g,hv⟩
 have he(x:ℝ)(h:x∈ Φ): F ↑x=f x:=by
    by_cases hp: -π < x; · change g ↑x=_; exact liftIoc_coe_apply (by rw [otherBand]; exact ⟨hp,h.2⟩)
    have hx:x=-π:=le_antisymm (le_of_not_gt hp) h.1
    subst x; change g ↑(-π) = f (-π); unfold g; rw [q]; have hy:= coe_add_period (2*π) (-π); rw [otherBand] at hy; rw [←hy]; exact liftIoc_coe_apply (by rw [otherBand]; exact ⟨by linarith [pi_pos], le_rfl⟩)
 have hz(n:ℤ): wrapT n f=fourierCoeff F (-n):=by
    rw [fourierCoeff_eq_intervalIntegral _ _ (-π),otherBand, intervalIntegral.integral_of_le (by linarith [pi_pos])]; simp only [neg_neg,benchmark,sound_neg]; unfold wrapT pluse; rw [Complex.real_smul,one_div, Complex.ofReal_inv]; congr 1; exact setIntegral_congr_fun paneM (fun x h'=> by rw [he x (Ioc_subset_Icc_self h')]; rfl)
 have H : Summable (fourierCoeff F):= ((Equiv.neg ℤ).summable_iff).1 (by simp_rw [hz] at h; exact h)
 let u:= has_pointwise_sum_fourier_series_of_summable H (↑t:AddCircle (2*π)); have hy:= (Equiv.neg ℤ).hasSum_iff.mpr u
 rw [← he t w]; simp_rw [hz]; simpa only [comp_def, smul_eq_mul, Equiv.neg_apply,benchmark,neg_neg] using hy
lemma sound_wrap (n k:ℤ) : wrapT n (soundT k)=if n=k then 1 else 0:=by
 have he:= congrFun (fourierCoeff_fourier (T:=2*π) (-k)) (-n); rw [fourierCoeff_eq_intervalIntegral _ _ (-π),otherBand] at he; simp only [neg_neg, benchmark, smul_eq_mul] at he; simp_rw [sound_neg] at he
 rw [intervalIntegral.integral_of_le (by linarith [pi_pos]), Complex.real_smul,one_div,Complex.ofReal_inv] at he; by_cases p:n=k <;> simpa [wrapT, screen, pluse, p] using he
end YM.CF.Crest.Sleet

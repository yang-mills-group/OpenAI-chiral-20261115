import YM.Spectral.Frequencies
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
/-! # Measure inversion bills (positive f, our plane radian char). -/
set_option autoImplicit false
noncomputable section
namespace YM.Caino
open Function Filter Set Metric NormedSpace Complex ContinuousLinearMap
open MeasureTheory Measure Boundary.Probe Boundary
open scoped NNReal ENNReal Topology InnerProductSpace ComplexConjugate ComplexOrder ContDiff BigOperators
variable {X:Type*}[NormedAddCommGroup X][InnerProductSpace ℝ X][FiniteDimensional ℝ X][MeasurableSpace X][BorelSpace X]
variable (μ:Measure X)[IsFiniteMeasure μ](t:X)
local notation "χ"=> charFun μ
abbrev inverted := ((pref X)⁻¹:ℝ) • (∫ z, χ z * plane t (-z))
def ombre: X→ℝ:=fun z=> (inverted μ z).re
local notation "Φ"=> ombre μ
variable (h:Integrable (charFun μ))
lemma realH : (↑(Φ t):ℂ)= inverted μ t:=by
 let f:=fun z=> χ z*plane t (-z); let x:=∫ z:X,f z
 have ht: star x=x:=by
   change conj _=_; rw [← integral_conj]; change (∫ z:X,star (f z))=x; refine Eq.trans ?_ (integral_neg_eq_self f volume); congr 1; funext z; unfold f; rw [charFun_neg, plane_inverse t (-z)]; exact star_mul' ..
 have hv: star (inverted μ t)= inverted μ t:= (star_smul ..).trans (by rw [star_trivial]; change _ • star x=_; rw [ht])
 simpa [ombre] using (conj_eq_iff_re.mp hv)
include h
lemma inverted_cont: Continuous (inverted μ):= (continuous_of_dominated (F:=fun t z:X=> χ z * plane t (-z))
 (fun _=> by unfold plane; fun_prop) (fun t=> ae_of_all _ fun z=>by simp) h.norm (ae_of_all _ fun z=>by unfold plane; fun_prop)).const_smul ((pref X)⁻¹:ℝ) -- fun_prop char
lemma ode_cont : Continuous Φ:= continuous_re.comp (inverted_cont μ h)
-- all ℂ marks compact
lemma bounty (f:X→ℂ)(p:HasCompactSupport f)(q:ContDiff ℝ ∞ f): (∫ x,f x∂μ)= ∫ x, ((↑(Φ x)):ℂ)*f x :=by
 let g:Probe X:= p.toSchwartzMap q; have hf:⇑g=f:= rfl
 let F(x y:X):= χ x * plane y (-x)*f y; have hv:Integrable (uncurry F) (volume.prod volume):=by
   have h':= q.continuous; refine (h.norm.mul_prod ((q.continuous.integrable_of_hasCompactSupport p).norm)).mono' ?_ (ae_of_all _ fun x=>?_)
   · change AEStronglyMeasurable (fun x:X × X=> χ x.1* plane x.2 (-x.1)*f x.2) _; exact ((((measurable_charFun (μ:=μ)).comp measurable_fst).mul (plane_cont.comp (continuous_snd.prodMk continuous_fst.neg)).measurable).mul (h'.measurable.comp measurable_snd)).aestronglyMeasurable
   simp [F,uncurry]
 have he:(∫ x, χ x * Probe.hat g x)=(∫ y, (∫ x, χ x * plane y (-x))*f y):=by
   calc _ = (∫ x, ∫ y, F x y) :=by simp_rw [Probe.hat_eq,←integral_const_mul,← mul_assoc]; rfl -- assoc flip
        _ = _:= (integral_integral_swap hv).trans (by unfold F; simp_rw [integral_mul_const])
 rw [Spectral.wave_integral,hf] at he
 simp_rw [realH,inverted,smul_mul_assoc, integral_smul]
 rw [← he, inv_smul_smul₀ (show pref X≠0 from prepos.ne')]
lemma realist (f:X→ℝ)(p:HasCompactSupport f)(q:ContDiff ℝ ∞ f): (∫ x,f x ∂μ)=∫ x, Φ x*f x:=by
 apply ofReal_injective; rw [← integral_complex_ofReal,← integral_complex_ofReal]
 simp_rw [ofReal_mul]; exact bounty μ h (ofReal ∘ f) (p.comp_left ofReal_zero) (ofRealCLM.contDiff.comp q)
lemma ombre_positive : 0 ≤ Φ t:=by
 by_contra! y; obtain ⟨δ,d,w⟩ := Metric.mem_nhds_iff.mp ((ode_cont μ h).continuousAt.tendsto.eventually (gt_mem_nhds y)); let B: ContDiffBump t:=⟨δ/2,δ,half_pos d,half_lt_self d⟩
 let f:=fun x:X=> -(Φ x)*(B x); have hf:Continuous f:= (ode_cont μ h).neg.mul B.continuous
 have hh(x:X)(p:B x≠0): x∈ ball t δ:= by have hx:x∈ support (fun y=> B y):=p; change x∈ support (⇑B) at hx; rwa [B.support_eq] at hx
 have hx : Integrable f:= hf.integrable_of_hasCompactSupport B.hasCompactSupport.mul_left
 have f_x(x:X):0 ≤ f x:= by
    unfold f; by_cases p:B x=0; · rw [p,mul_zero]
    exact mul_nonneg (neg_nonneg.mpr (le_of_lt (show Φ x<0 from w (hh x p)))) B.nonneg -- tune whitespace
 have hp:t∈ support f:= by change f t≠0; unfold f; rw [B.one_of_mem_closedBall (mem_closedBall_self (B.rIn_pos).le),mul_one]; simp [ne_of_lt y] -- simp center
 have hz:0<∫ x,f x:= (integral_pos_iff_support_of_nonneg f_x hx).2 ((isOpen_ne_fun hf continuous_const).measure_pos volume ⟨t,hp⟩)
 have ha:0 ≤ ∫ x,B x ∂μ := integral_nonneg fun _=> B.nonneg
 rw [realist μ h B B.hasCompactSupport B.contDiff] at ha; unfold f at hz; simp_rw [neg_mul, integral_neg] at hz; linarith
def chisels {Z:Type*}[MeasurableSpace Z] (f:Z→ℝ) (μ:Measure Z): Measure Z:= μ.withDensity (ENNReal.ofReal ∘ f)
omit h in
lemma carves (η₀:Measure X) (g:X→ℝ)(hg:Measurable g)(w:∀ x,0 ≤ g x)(f:X→ℂ): (∫ x, f x∂ chisels g η₀)=(∫ x, (g x:ℂ)*f x∂η₀):= by
 unfold chisels; rw [integral_withDensity_eq_integral_toReal_smul (ENNReal.measurable_ofReal.comp hg) (Eventually.of_forall fun x=> (ENNReal.ofReal_lt_top))]; simp_rw [Function.comp_apply, ENNReal.toReal_ofReal (w _), Complex.real_smul]
omit h in
private lemma sun_gains(μ:Measure X) (f:X→ℝ)(p:Integrable f μ)(t:∀ x,0 ≤ f x): IsFiniteMeasure (chisels f μ):= isFiniteMeasure_withDensity ((lintegral_ofReal_ne_top_iff_integrable p.1 (ae_of_all _ t)).2 p)
-- actual equality on bump-block & then all
theorem densityLaw : μ=chisels (Φ) volume:=by
 let ν:= chisels (Φ) volume; haveI : IsLocallyFiniteMeasure ν:= IsLocallyFiniteMeasure.withDensity_ofReal (ode_cont μ h)
 let S(n:ℕ):= closedBall (0:X) n; let Z:= ⋃ i:ℕ,S i
 suffices g: ∀ i:ℕ, μ.restrict (S i)=ν.restrict (S i) by
   have he:μ.restrict Z=ν.restrict Z:= restrict_iUnion_congr.mpr g; simpa only [show Z=univ from iUnion_closedBall_nat _,restrict_univ] using he
 intro n; let B:ContDiffBump (0:X):= ⟨(n:ℝ)+1,n+2,(by positivity),by linarith⟩; let f: X→ℝ:= B; have hf: Measurable f:= B.continuous.measurable; have hp(x:X):0 ≤ f x:= B.nonneg
 have he(η:Measure X):η.restrict (S n)=(chisels f η).restrict (S n):= by
   unfold chisels; rw [restrict_withDensity measurableSet_closedBall]; refine Eq.symm ((withDensity_congr_ae ?_).trans withDensity_one); filter_upwards [ae_restrict_mem (μ:=η) (s:=S n) measurableSet_closedBall] with x hx
   have hy:f x=1:= B.one_of_mem_closedBall (closedBall_subset_closedBall (show (n:ℝ) ≤ (n:ℝ)+1 by linarith) hx); rw [Function.comp_apply,hy]; simp
 have h':chisels f μ=chisels f ν:=by
     have H'(η:Measure X)[IsLocallyFiniteMeasure η]: IsFiniteMeasure (chisels f η):= sun_gains η f (B.continuous.integrable_of_hasCompactSupport B.hasCompactSupport) hp; letI:= H' μ; letI:=H' ν -- tune parse
     apply Measure.ext_of_charFun; funext k; let v:=fun x:X=> plane x k; let qf(x:X):=((f x:ℂ)*v x)
     have hq:ContDiff ℝ ∞ qf:= (ofRealCLM.contDiff.comp B.contDiff).mul (show ContDiff ℝ ∞ v from (by unfold v plane; exact (((ofRealCLM.contDiff.comp (contDiff_id.inner ℝ contDiff_const)).mul contDiff_const).cexp)))
     change (∫ x,v x ∂chisels f μ)=∫ x,v x ∂chisels f ν; rw [carves μ f hf hp,carves ν f hf hp]; exact (bounty μ h qf ((B.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right) hq).trans (carves volume (ombre μ) (ode_cont μ h).measurable (fun x=> ombre_positive μ x h) qf).symm
 exact (he μ).trans ((congrArg (fun x:Measure X=> x.restrict (S n)) h').trans (he ν).symm)
end YM.Caino
#print axioms YM.Caino.densityLaw

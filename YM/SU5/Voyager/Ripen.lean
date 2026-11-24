import YM.SU5.Voyager.Poppy
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
/-! # REAL local density seen analytically on every line through interior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Caino
open Function Filter Set Metric NormedSpace Bornology Complex
open MeasureTheory Measure Boundary.Probe Boundary
open scoped NNReal ENNReal Topology InnerProductSpace ComplexConjugate ComplexOrder BigOperators
section issue
variable {X:Type*}[MeasurableSpace X](μ:Measure X){f g:X→ℝ}
lemma colors (u:Measurable f)(v:Measurable g)(b:∀ x,0 ≤ f x): chisels g (chisels f μ)= chisels (f*g) μ:=by
 unfold chisels; rw [← withDensity_mul _ (by fun_prop) (by fun_prop)]; congr 1; funext x; exact (ENNReal.ofReal_mul (b x)).symm -- last arg?
lemma foil(x:Set X)(h:MeasurableSet x): (chisels f μ).restrict x=chisels f (μ.restrict x):=restrict_withDensity h _
lemma tess [SigmaFinite μ](u:Measurable f)(v:Measurable g)(b:∀ x,0 ≤ f x)(c:∀ x,0 ≤ g x)(h: chisels f μ = chisels g μ): f=ᵐ[μ] g:=( (withDensity_eq_iff_of_sigmaFinite (μ:=μ) (f:=ENNReal.ofReal ∘ f) (g:=ENNReal.ofReal ∘ g) (by fun_prop) (by fun_prop)).1 h).mono fun x h=> (ENNReal.ofReal_eq_ofReal_iff (b x) (c x)).1 h -- check
lemma dimMask (S:Set X)(x:MeasurableSet S)(p:Measurable f)(q:∀ z∈S,0<f z)(t:∀ x,0 ≤ f x) : μ.restrict S=chisels f⁻¹ ((chisels f μ).restrict S):=by
 rw [foil _ _ x, colors _ p p.inv t]; unfold chisels; refine ((withDensity_congr_ae ?_).trans withDensity_one).symm; filter_upwards [ae_restrict_mem x] with v y; change ENNReal.ofReal (f v*(f v)⁻¹)=1; rw [mul_inv_cancel₀ (q v y).ne']; simp
end issue
variable {X:Type*}[NormedAddCommGroup X][InnerProductSpace ℝ X][FiniteDimensional ℝ X][MeasurableSpace X][BorelSpace X]
variable (μ:Measure X)(W:X→ℝ)(p d:X)
local notation "l[" z "]"=> (p+(z:ℝ) • d)
def serves (n:ℕ) := chisels (W^n) μ
structure Furnished : Prop where
 paid : ∀ i:ℕ, IsFiniteMeasure (serves μ W i)
 tempo : Continuous W
 nonneg : ∀ x,0 ≤ W x
 alt : ∀ p d:X,∃ u:ℂ→ℂ, Differentiable ℂ u ∧ ∀ z:ℝ,u z=W (p+z • d)
 bursts : FlairC (fun i=> charFun (serves μ W i))
variable {μ W}
namespace Furnished
variable (H:Furnished μ W)
local notation "ν" i:max=> serves μ W i
local notation "χ" i:max=> ombre (ν i)
include H
lemma upcasts : ∀ᶠ n in atTop, Integrable (charFun (ν n)) := by obtain ⟨A,h,H⟩:=dustFare H.bursts zero_lt_one zero_lt_one; exact H.mono fun i y=>y.1
protected noncomputable def height : ℕ:=(H.upcasts.exists).choose
lemma reward (n:ℕ):Measurable (W^n):= (H.tempo.pow n).measurable
lemma stymie (n:ℕ)(x:X):0≤(W^n) x:=pow_nonneg (H.nonneg _) _
variable {m n:ℕ}(p₀:Integrable (charFun (serves μ W m)))
include p₀ in
lemma scalesM (q:Integrable (charFun (serves μ W n))) : (χ m) * W^n =(χ n)* W^m:=by
 letI:=H.paid; have ht(i:ℕ)(u:Integrable (charFun (ν i)))(j:ℕ): chisels ((χ i)*W^j) volume= chisels ((W^i)*W^j) μ:= by rw [←colors _ (ode_cont (ν i) u|>.measurable) (H.reward j) (fun x=> ombre_positive (ν i) x u),← densityLaw _ u]; exact colors μ (H.reward i) (H.reward j) (H.stymie i)
 have he(i j:ℕ)(u:Integrable (charFun (ν i))):Continuous ((χ i)*W^j):=(ode_cont (ν i) u).mul (H.tempo.pow j)
 have h(i j:ℕ)(u:Integrable (charFun (ν i)))(x:X):0 ≤ ((χ i)*W^j) x:=mul_nonneg (ombre_positive (ν i) x u) (H.stymie j x)
 exact eq_of_ae_eq (tess volume (he m n p₀).measurable (he n m q).measurable (h _ _ p₀) (h _ _ q) (by rw [ht m p₀,ht n q,mul_comm (W^m)])) (he m n p₀) (he n m q)
noncomputable def portrait: X→ℝ:=(ombre (serves μ W H.height))/W^H.height
lemma aligned {n:ℕ}(p:Integrable (charFun (ν n)))(x:X)(h:0<W x): H.portrait x=(χ n) x /(W x)^n:=by
 let m:=H.height; have hm:Integrable (charFun (ν m)):= H.upcasts.exists.choose_spec; apply (div_eq_div_iff (pow_pos h m|>.ne') ((pow_pos h n).ne')).mpr; exact congrFun (H.scalesM hm p) x
lemma portLoc (U:Set X)(r:MeasurableSet U)(h:∀ x∈ U,0<W x): μ.restrict U= chisels H.portrait (volume.restrict U):=by
 let n:=H.height; have ht:Integrable (charFun (ν n)):=H.upcasts.exists.choose_spec; letI:=H.paid; have hv:μ.restrict U=chisels (W^n)⁻¹ ((chisels ((χ n)) volume).restrict U):=by rw [← densityLaw _ ht]; exact dimMask μ U r (H.reward n) (fun x p=>pow_pos (h _ p) n) (H.stymie n)
 refine hv.trans ?_; rw [foil _ _ r, colors _ (ode_cont (ν n) ht).measurable ((H.reward n).inv) (fun x=> ombre_positive (ν n) x ht)]; unfold portrait; rw [div_eq_mul_inv]
lemma portrait_m : Measurable H.portrait:=by letI:=H.paid; exact ((ode_cont (ν H.height) (H.upcasts.exists.choose_spec)).measurable).div (H.reward _)
lemma port_p(x:X):0 ≤ H.portrait x:=by letI:=H.paid; exact div_nonneg (ombre_positive _ x H.upcasts.exists.choose_spec) (H.stymie _ x)
lemma port_t(x:X)(h:0<W x):ContinuousAt H.portrait x:=by
 letI:=H.paid; exact (ode_cont _ H.upcasts.exists.choose_spec).continuousAt.div (H.tempo.continuousAt.pow _) (pow_pos h _|>.ne') -- subtle
lemma lush (t:0<W p):AnalyticAt ℝ (fun z:ℝ=> H.portrait (p+z • d)) 0:=by
 letI:= H.paid; obtain ⟨u,a,b⟩:= H.alt p d; let x:= W p/2 ; have hp:0<x:=(by positivity); let T:= (ofReal ∘ fun z:ℝ=> H.portrait (p+z • d))
 obtain ⟨A,h,h'⟩:= harvest_crops p d H.bursts (x/2) (by positivity); have he:u 0= W p:= by simpa using b 0
 obtain ⟨R,hR,P⟩:= Metric.mem_nhds_iff.mp ((a.continuous.norm.continuousAt.tendsto).eventually (lt_mem_nhds (show x<‖u 0‖ from (by rw [he,norm_real,Real.norm_eq_abs,abs_of_pos t]; exact half_lt_self t))))
 let D:=R/2; have v:0<D:=(by positivity); let H':Set ℂ:= closedBall 0 D
 have hy(z:ℂ)(p:z∈H'): x<‖u z‖:= P (closedBall_subset_ball (half_lt_self hR) p)
 have hb(z:ℂ)(p:z∈H'): u z≠0:= norm_pos_iff.mp (hp.trans (hy z p))
 let f(i:ℕ):=fun z:ℂ=> gesture p d A i (serves μ W) z / u z^i; obtain ⟨C,hc,g⟩:= flourishes p d A H.bursts D v h
 have hg: AnalyticAt ℝ T 0:= by
    apply golden_arc (k:=1/2) (c:=C/x) v (by positivity) (by norm_num) (by positivity) f
    · filter_upwards [g] with n ht; refine ⟨ht.1.differentiableOn.div (a.pow n|>.differentiableOn) (fun z p=> pow_ne_zero _ (hb z p)), fun z p=>?_⟩
      unfold f; rw [norm_div,norm_pow,div_pow]; exact div_le_div₀ (by positivity) (ht.2 z p) (by positivity) (pow_le_pow_left₀ hp.le (hy z p).le _)
    filter_upwards [h'] with n ht; intro z hz
    have hp₁:(z:ℂ)∈H':= by simpa [H',Real.norm_eq_abs] using hz
    have hw :‖u z‖= W (l[z]):= by rw [b,norm_real,Real.norm_eq_abs,abs_of_nonneg (H.nonneg _)]
    have hv:x ≤ W (l[z]):=(hy _ hp₁).le.trans_eq hw; have hs:=H.aligned ht.1 l[z] (lt_of_lt_of_le hp hv)
    unfold f T; simp only [Function.comp_apply]; rw [b z,hs,ofReal_div, ofReal_pow, realH, ← sub_div,norm_div, norm_pow, norm_real,Real.norm_eq_abs,abs_of_nonneg (H.nonneg _)]
    refine (div_le_div₀ (by positivity : 0 ≤ (x/2)^n) (ht.2 z) (pow_pos hp _) (pow_le_pow_left₀ hp.le hv _)).trans_eq ?_; rw [← div_pow, show (x/2)/x=1/2 from (by field_simp)]
 exact (reCLM.analyticAt (T 0)).comp hg -- defeq?
end Furnished
end YM.Caino
#print axioms YM.Caino.Furnished.portLoc
#print axioms YM.Caino.Furnished.lush

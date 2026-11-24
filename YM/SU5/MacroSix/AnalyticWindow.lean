import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Topology
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Frequency windows for compact smear tests

Slicing proof of nullity of zeros, on plain ℝⁿ. Analyticity only charged along
individual lines. Fourier in angular frequency convention, no `2 π`. -/

set_option autoImplicit false
noncomputable section
namespace YM.MacroSix
open Filter Function Metric Set MeasureTheory Complex
open scoped Topology InnerProductSpace BigOperators

private lemma slice_analytic_cost (g : ℝ → ℂ) (h : AnalyticOnNhd ℝ g univ) (p : g 0 ≠ 0) :
    ∀ᵐ x : ℝ, g x ≠ 0 := by
  have ht := h.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ
  rcases ht with ht | ht
  · exact (p (ht (Set.mem_univ (0:ℝ)))).elim
  simpa using (ht.filter_mono (ae_restrict_le_codiscreteWithin (μ:=(volume:Measure ℝ)) MeasurableSet.univ))

theorem lineAnalytic_null (n : ℕ) (g : (Fin n → ℝ) → ℂ) (q : Measurable g)
    (h : ∀ a b : Fin n → ℝ, AnalyticOnNhd ℝ (fun t : ℝ ↦ g (a+t • b)) univ)
    (p : g 0 ≠ 0) : ∀ᵐ x, g x ≠ 0 := by
  induction n with
  | zero => exact ae_of_all _ (fun x ↦ (Subsingleton.elim (0:Fin 0 → ℝ) x) ▸ p)
  | succ n ih =>
    let E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ ℝ) 0
    let u (x : Fin n → ℝ) := Fin.cons (α:=fun _ ↦ ℝ) 0 x
    have hu (x : ℝ × (Fin n → ℝ)) : E.symm x = Fin.cons (α:= fun _ ↦ ℝ) x.1 x.2 := by
      simp [E,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Fin.insertNth_zero']
    have hv (x : Fin n → ℝ) : E.symm (0,x)=u x := hu _
    have h0 : u 0=0 := by ext i; refine Fin.cases ?_ (fun i ↦ ?_) i <;> simp [u]
    have ht : ∀ᵐ x : Fin n → ℝ, g (u x) ≠ 0 := by
      refine ih (g ∘ u) (q.comp ?_) (fun a b ↦ ?_) (show g (u 0) ≠ 0 by rwa [h0])
      · simp_rw [show u=fun x ↦ E.symm (0,x) from (funext hv).symm]
        exact E.symm.measurable.comp (measurable_const.prodMk measurable_id)
      have he (t : ℝ) : u (a+t • b)=u a+t • u b := by
        ext i; refine Fin.cases ?_ (fun i ↦ ?_) i <;> simp [u]
      simp_rw [Function.comp_apply, he]; exact h _ _
    have hm : MeasurableSet {p : ℝ × (Fin n → ℝ) | g (E.symm (p.1,p.2)) ≠ 0} :=
      ((measurableSet_singleton (0:ℂ)).preimage (q.comp E.symm.measurable)).compl
    have hr : ∀ᵐ x : ℝ × (Fin n → ℝ), g (E.symm x) ≠ 0 := by
      refine (Measure.ae_prod_iff_ae_ae hm).mpr ((Measure.ae_ae_comm (μ:=(volume:Measure ℝ)) hm).mpr (ht.mono ?_))
      intro x p
      apply slice_analytic_cost (fun t ↦ g (E.symm (t,x))) ?_ (by rw [hv]; exact p)
      let b := Fin.cons (α:=fun _ : Fin (n+1) ↦ ℝ) (1:ℝ) (0 : Fin n → ℝ)
      have he (t : ℝ) : E.symm (t,x) = u x+t • b := by
        rw [hu]; ext i; refine Fin.cases ?_ (fun i ↦ ?_) i <;> simp [u,b]
      simp_rw [he]; exact h _ _
    filter_upwards [(volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ ℝ) 0).quasiMeasurePreserving.ae hr]
      with x ht
    exact fun p ↦ ht (by change g (E.symm (E x)) = _; rwa [E.symm_apply_apply])

section frequency
variable {n : ℕ}
local notation "X" => (Fin n → ℝ)

def wavePhase (p x : X) : ℂ := Complex.exp (↑(∑ j, p j*x j)*Complex.I)
lemma phase_unit (p x : X) : ‖wavePhase p x‖=1 := by simp [wavePhase, Complex.norm_exp]

def frequencyCost (g : X → ℝ) (p : X) : ℂ := ∫ x, (g x:ℂ) * wavePhase p x

private lemma envelope_mem {E : Type*} [Zero E] {g : X → ℝ} (h : HasCompactSupport g) (f : X → E)
    (p : ∀ x, g x=0 → f x=0) : HasCompactSupport f :=
  HasCompactSupport.of_support_subset_isCompact h fun x v ↦ subset_tsupport _ (mt (p x) v)

lemma frequencyCost_cont {g : X → ℝ} (p : Continuous g) (h : HasCompactSupport g) :
    Continuous (frequencyCost g) := by
  let F (v : X) (x : X) := (g x:ℂ)*wavePhase v x
  refine continuous_of_dominated (F:=F) ?_ (bound:=fun x ↦ ‖g x‖) ?_
    (p.norm.integrable_of_hasCompactSupport h.norm) ?_
  · exact fun v ↦ (show Continuous (F v) by unfold F wavePhase; fun_prop).aestronglyMeasurable
  · exact fun v ↦ ae_of_all _ (fun x ↦ by simp [F,phase_unit])
  exact ae_of_all _ (fun i ↦ by unfold F wavePhase; fun_prop)

private lemma integratedLine (g : X → ℝ) (p : Continuous g) (h : HasCompactSupport g)
    (U V : X → ℂ) (hc : Continuous U) (hV : Continuous V) :
    Differentiable ℂ fun z ↦ ∫ x, (g x : ℂ) * Complex.exp (U x + z*V x) := by
  let F (z : ℂ) (x : X) := (g x:ℂ) * Complex.exp (U x + z*V x)
  let G (z : ℂ) (x : X) := F z x * V x
  have he (z : ℂ) : Continuous (F z) := by unfold F; fun_prop
  have hx : Continuous (Function.uncurry G) := by unfold Function.uncurry G F; fun_prop
  intro z
  let D := closedBall z 1
  let K := tsupport g
  have hK : IsCompact K := h
  obtain ⟨C,H⟩ := (isCompact_closedBall z 1|>.prod hK).bddAbove_image hx.norm.continuousOn
  let B := K.indicator fun _ ↦ C
  have hB : Integrable B := (integrable_indicator_iff hK.measurableSet).mpr
    (integrableOn_const hK.measure_lt_top.ne)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=F) (F':=G)
    (closedBall_mem_nhds z zero_lt_one) (Eventually.of_forall fun x ↦ (he x).aestronglyMeasurable)
    ((he z).integrable_of_hasCompactSupport (envelope_mem h _ (fun x y ↦ by simp [F,y])))
    ((he z).mul hV).aestronglyMeasurable ?_ hB ?_).2.differentiableAt
  · apply ae_of_all; intro x w p; by_cases e : x ∈ K
    · rw [show B x=C from Set.indicator_of_mem e _]; exact H ⟨(w,x),⟨p,e⟩,rfl⟩
    have hx : g x=0 := image_eq_zero_of_notMem_tsupport e
    simp [B,e,G,F,hx]
  apply ae_of_all; intro x w p
  have he := (((((hasDerivAt_id' w).mul_const (V x)).const_add (U x)).cexp).const_mul (↑(g x):ℂ))
  simpa only [Function.comp_def, one_mul,G,F,mul_assoc] using he

lemma frequencyCost_line {g : X → ℝ} (p : Continuous g) (h : HasCompactSupport g)
    (a b : X) : AnalyticOnNhd ℝ (fun t : ℝ ↦ frequencyCost g (a+t • b)) univ := by
  let V (p x : X) := (↑(∑ i, p i*x i):ℂ)*Complex.I
  let F (z : ℂ) := ∫ x, (g x:ℂ) * Complex.exp (V a x + z*V b x)
  have he : Differentiable ℂ F := integratedLine g p h _ _ (by unfold V; fun_prop) (by unfold V; fun_prop)
  have ht (x : X) (t : ℝ) : V (a+t • b) x = V a x + (t:ℂ)*V b x := by
    unfold V; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc, ← Finset.mul_sum,
      Finset.sum_add_distrib]; push_cast; ring
  have hh (t : ℝ) : frequencyCost g (a+t • b)= F t := by
    unfold frequencyCost; simp_rw [show ∀ (p x : X), wavePhase p x = Complex.exp (V p x) from (fun _ _ ↦ rfl), ht]; rfl
  simp_rw [hh]
  intro x _
  have hx := (he.differentiableOn.analyticAt (univ_mem : (Set.univ : Set ℂ) ∈ 𝓝 (x:ℂ))).restrictScalars (𝕜:=ℝ)
  exact hx.comp (Complex.ofRealCLM.analyticAt _)

lemma frequencyCost_zero {g : X → ℝ} (q : ∫ x, g x = 1) : frequencyCost g 0 = 1 := by
  unfold frequencyCost; simp [wavePhase, integral_complex_ofReal, q]

theorem frequencyCost_pay {g : X → ℝ} (p : Continuous g) (h : HasCompactSupport g)
    (q : ∫ x, g x = 1) : ∀ᵐ x, frequencyCost g x ≠ 0 := lineAnalytic_null n _
  (frequencyCost_cont p h).measurable (frequencyCost_line p h) ((frequencyCost_zero q).symm ▸ one_ne_zero)

end frequency
end YM.MacroSix
#print axioms YM.MacroSix.frequencyCost_pay

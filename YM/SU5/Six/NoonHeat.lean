import YM.SU5.Six.Interior
import YM.SU5.Six.Night
set_option autoImplicit false
noncomputable section

namespace YM.Six
open MeasureTheory Filter Spectral OS Semigroup Balloon Cheer Boundary Probe
open scoped Topology InnerProductSpace ComplexConjugate NNReal ComplexOrder

/-- Continuity of costs in an auxiliary parameter. -/
lemma HalfLimit.parametrized {X : Type*} [UniformSpace X] [WeaklyLocallyCompactSpace X]
    {f : X → E4 → ℂ} (hf : Continuous (Function.uncurry f)) (hb : ∃ C:ℝ, ∀ x p, p∈half → ‖f x p‖ ≤ C)
    {q : ℕ → X} {y : X} (hq : Tendsto q atTop (𝓝 y)) : HalfLimit (f ∘ q) (f y) := by
  have h (x) : Continuous (f x) := hf.comp (f:=fun z => (x,z)) (by fun_prop)
  refine ⟨fun i => (h _).measurable.comp measurable_subtype_coe,
    hb.imp (fun _ w i => w _), (h y).continuousOn,?_⟩
  intro K hK _
  letI := isCompact_iff_compactSpace.mp hK
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe,Metric.tendstoUniformly_iff]
  let g (x : X) (p : K) := f x (p:E4)
  have hv : TendstoUniformly g (g y) (𝓝 y) := Continuous.tendstoUniformly _
    (hf.comp (f:=fun z : X × K => (z.1,(z.2:E4))) (by fun_prop)) _
  exact fun e he => hq.eventually (Metric.tendstoUniformly_iff.mp hv e he)

lemma fade_bound (t : ℝ≥0) (p : E4) (hp : p∈half) : ‖fade t p‖≤1 := by
  rw [fade,Complex.norm_real,Real.norm_of_nonneg (show 0 ≤ tinct timeAxis t p from (Real.exp_pos _).le)]
  exact fuel _ _ hp
lemma tapered_bound (y : Space3) (d t : ℝ≥0) (p : E4) (hp : p∈half) : ‖tapered y d t p‖≤4 := by
  have h : ‖(1:ℂ)- fade t p‖≤2 := by
    calc
      _ ≤ _ := norm_sub_le ..
      _ ≤ _ := by rw [norm_one]; linarith [fade_bound t p hp]
  rw [tapered, norm_mul, norm_pow,norm_mul,phasor,show ‖plane ..‖=1 from by simp,one_mul]
  calc
    _ ≤ (1:ℝ) * 2^2 := by gcongr; exact fade_bound _ _ hp
    _ = 4 := by norm_num

lemma tapered_limit {y : ℕ → Space3} {t : ℕ → ℝ≥0} (hy : Tendsto y atTop (𝓝 0))
    (ht : Tendsto t atTop (𝓝 (1/2))) :
    HalfLimit (fun i => tapered (y i) 10 (t i)) (tapered 0 10 (1/2)) := by
  let f (z : Space3 × ℝ≥0) := tapered z.1 10 z.2
  refine HalfLimit.parametrized (q:=fun i=>(y i,t i)) (y:=(0,1/2)) (f:=f) ?_ ⟨4,fun z => tapered_bound z.1 10 z.2⟩
    (hy.prodMk_nhds ht)
  unfold f
  unfold Function.uncurry
  -- unfold tapered
  change Continuous (fun p : (Space3 × ℝ≥0) × E4 => tapered p.1.1 10 p.1.2 p.2)
  unfold tapered phasor fade plane tinct
  fun_prop

/-- Limiting tapering, positive on interior. -/
lemma tapered_positive (μ : Measure E4) [IsFiniteMeasure μ]
    (hs : ∀ᵐ p ∂μ, p∈half)
    (hi : ∀ ⦃U : Set E4⦄, IsOpen U → (Mink.inside ∩ U).Nonempty → 0 < μ U) :
    0 < ∫ p, tapered 0 10 (1/2) p ∂μ := by
  let g : E4→ℝ := fun p=> tinct timeAxis 10 p * (1-tinct timeAxis (1/2) p)^2
  have h (p : E4) : tapered 0 10 (1/2) p = g p := by simp [g,tapered,phasor,fade]
  simp_rw [h]
  let p := YM.basis timeAxis
  refine interior_positive hs hi g ?_ ?_ 4 ?_ p ?_ ?_
  · unfold g tinct; fun_prop
  · intro p _; unfold g tinct; positivity
  · intro p hp; have he := tapered_bound 0 10 (1/2) p hp
    rw [h,Complex.norm_real,Real.norm_eq_abs] at he
    exact le_trans (le_abs_self _) he
  · change ‖spatial _‖ < time _
    rw [Mink.roll_clock, Mink.roll_space,norm_zero]; norm_num
  apply mul_pos (Real.exp_pos _) (pow_pos ?_ 2)
  have ht : p timeAxis = 1 := Mink.roll_clock
  rw [sub_pos,tinct,Real.exp_lt_one_iff, ht]; norm_num

lemma tapered_zoom {ρ:ℝ≥0} (h : 0 < ρ) (y : Space3) (t : ℝ≥0) (p : E4) :
    tapered (((ρ:ℝ))⁻¹ • y) 10 (t/ρ) (zoom ρ p) = tapered y (10*ρ) t p := by
  unfold tapered
  have he : (ρ:ℝ) ≠ 0 := ne_of_gt h
  have h₁ : phasor ((ρ:ℝ)⁻¹ • y) (zoom ρ p) = phasor y p := by
    rw [phasor,phasor,zoom,Mink.rest_mul,plane,plane,real_inner_smul_right,real_inner_smul_left,
      inv_mul_cancel_left₀ he]
  rw [h₁]
  simp only [fade,tinct, zoom, PiLp.smul_apply, smul_eq_mul, NNReal.coe_div,NNReal.coe_mul]
  rw [← mul_assoc (↑(10:ℝ≥0):ℝ),← mul_assoc,div_mul_cancel₀ _ he]

end YM.Six

import YM.SU5.MacroSix.MeasureMatrix

/-!
# Compact-uniform tests on the zoomed positive half-space

Use a fixed budget for the functions (not compact support); tightness needed here
is eventual, not a running height chosen by `support f`. We state the test
hypotheses only on the closed half-space (using the clamped versions for Borelness).
-/

set_option autoImplicit false
noncomputable section

namespace YM.Cheer.MatrixZoom

open Filter Metric Set Function MeasureTheory Mink
open scoped Topology NNReal ENNReal InnerProductSpace BigOperators BoundedContinuousFunction

def positiveHalf : Set E4 := {x | 0 ≤ time x}
lemma positiveHalf_closed : IsClosed positiveHalf := isClosed_le continuous_const clock_cont
lemma zero_energy_mem : (0 : E4) ∈ positiveHalf := by simp [positiveHalf]

/-- No continuity or costs required in negative energy. -/
def clampEnergy (x : E4) := position (spatial x) (max (time x) 0)
lemma clampContinuous : Continuous clampEnergy :=
  divide.symm.continuous.comp (rest_cont.prodMk (clock_cont.max continuous_const))
lemma clampHalf (x : E4) : clampEnergy x ∈ positiveHalf := by simp [clampEnergy,positiveHalf]
lemma clampId (x : E4) (h : x ∈ positiveHalf) : clampEnergy x = x := by
  rw [clampEnergy,max_eq_left h,position_eta]

/-- Uniformly bounded, compact-uniform convergence on nonnegative energy; the limit
is *continuous on that closed half-space*. Measurability of clamp composite is a way to
ask Borel there only. -/
structure ZoomTest (F : ℕ → E4 → ℂ) (f : E4 → ℂ) : Prop where
  cont : ContinuousOn f positiveHalf
  borel : ∀ i, Measurable (F i ∘ clampEnergy)
  bounded : ∃ C : ℝ, 0 < C ∧ (∀ x ∈ positiveHalf, ‖f x‖ ≤ C) ∧
    (∀ i, ∀ x ∈ positiveHalf, ‖F i x‖ ≤ C)
  cost : ∀ K : Set E4, K ⊆ positiveHalf → IsCompact K → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ i in atTop, ∀ x ∈ K, ‖F i x - f x‖ ≤ ε

lemma ZoomTest.continuous_clamp {F f} (X : ZoomTest F f) : Continuous (f ∘ clampEnergy) :=
  continuousOn_univ.mp (X.cont.comp clampContinuous.continuousOn fun x _ ↦ clampHalf x)

lemma ZoomTest.const (f : E4 → ℂ) (h : ContinuousOn f positiveHalf)
    (t : ∃ C : ℝ, ∀ x ∈ positiveHalf, ‖f x‖ ≤ C) : ZoomTest (fun _ ↦ f) f := by
  have he : Continuous (f ∘ clampEnergy) :=
    continuousOn_univ.mp (h.comp clampContinuous.continuousOn fun x _ ↦ clampHalf x)
  obtain ⟨C,H⟩ := t
  have hc : 0 ≤ C := (norm_nonneg _).trans (H _ zero_energy_mem)
  have hw : ∀ x ∈ positiveHalf, ‖f x‖ ≤ C + 1 := fun x h ↦ (H x h).trans (by linarith)
  exact ⟨h,fun _ ↦ he.measurable,⟨C+1,by linarith,hw,fun _ ↦ hw⟩,
    fun _ _ _ _ t ↦ Eventually.of_forall (fun _ _ _ ↦ by simpa using t.le)⟩

variable {μ : Narrow} {U : ℕ → Narrow} {F : ℕ → E4 → ℂ} {f : E4 → ℂ}
local notation "M" => Measure E4

lemma clampAE {g : E4 → ℂ} (h : Brilliant μ) : g ∘ clampEnergy =ᵐ[(μ:M)] g :=
  h.mono fun x p ↦ congrArg g (clampId x p)

lemma ZoomTest.target (h : Brilliant μ) (t : ZoomTest F f) :
    Integrable f (μ:M) := by
  obtain ⟨C,-,g,-⟩ := t.bounded
  refine Integrable.congr (f:= f ∘ clampEnergy) ?_ (clampAE h)
  exact (integrable_const C).mono' t.continuous_clamp.aestronglyMeasurable
    (ae_of_all _ fun x ↦ g _ (clampHalf x))

lemma ZoomTest.each (h : Brilliant μ) (t : ZoomTest F f) (i : ℕ) :
    Integrable (F i) (μ:M) := by
  obtain ⟨C,-,-,g⟩ := t.bounded
  refine Integrable.congr (f:= F i ∘ clampEnergy) ?_ (clampAE h)
  exact (integrable_const C).mono' (t.borel i).aestronglyMeasurable
    (ae_of_all _ fun x ↦ g i _ (clampHalf x))

private lemma smallClosedComplement (h : Tendsto U atTop (𝓝 μ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ), ∀ᶠ i in atTop, (U i:M).real ((ball (0:E4) (n:ℝ))ᶜ) < ε := by
  let A (n : ℕ) := (ball (0:E4) (n:ℝ))ᶜ
  have ha : Antitone A := fun i j q ↦ compl_subset_compl.mpr
    (Metric.ball_subset_ball (by exact_mod_cast q))
  have he : ⋂ i, A i = ∅ := by
    ext x; change (_ ↔ False); simp only [mem_iInter, iff_false, not_forall]
    obtain ⟨i,H⟩ := exists_nat_gt (dist x 0)
    exact ⟨i, fun p ↦ p H⟩
  have hh (i : ℕ) : IsClosed (A i) := isOpen_ball.isClosed_compl
  have ht := tendsto_measure_iInter_atTop (μ:=(μ:M))
    (fun n ↦ (hh n).measurableSet.nullMeasurableSet) ha ⟨0, measure_ne_top _ _⟩
  rw [he,measure_empty] at ht
  obtain ⟨n,p⟩ := (ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hε))).exists
  refine ⟨n,?_⟩
  have hx := FiniteMeasure.limsup_measure_closed_le_of_tendsto h (hh n)
  exact (eventually_lt_of_limsup_lt (hx.trans_lt p)).mono fun i q ↦
    ENNReal.toReal_lt_of_lt_ofReal q

private lemma targetLimit (h : Tendsto U atTop (𝓝 μ)) (hU : ∀ i, Brilliant (U i))
    (hμ : Brilliant μ) (t : ZoomTest F f) :
    Tendsto (fun i ↦ ∫ x, f x ∂(U i:M)) atTop (𝓝 (∫ x, f x ∂(μ:M))) := by
  obtain ⟨C,-,hc,-⟩ := t.bounded
  let g := f ∘ clampEnergy
  have he (x : E4) : ‖g x‖ ≤ C := hc _ (clampHalf x)
  let G := BoundedContinuousFunction.mkOfBound ⟨g,t.continuous_clamp⟩ (C+C)
    (fun x y ↦ (show dist (g x) (g y) ≤ _ from
      (dist_le_norm_add_norm _ _).trans (add_le_add (he x) (he y))))
  have hb (μ : Narrow) (p : Brilliant μ) : (∫ x, G x ∂(μ:M)) = (∫ x, f x ∂(μ:M)) :=
    integral_congr_ae (clampAE p)
  rw [← hb _ hμ]
  exact ((FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp h G).congr
    fun i ↦ hb _ (hU i)

private lemma diffLimit (h : Tendsto U atTop (𝓝 μ)) (hU : ∀ i, Brilliant (U i))
    (t : ZoomTest F f) :
    Tendsto (fun i ↦ (∫ x, F i x ∂(U i:M)) - ∫ x, f x ∂(U i:M)) atTop (𝓝 0) := by
  obtain ⟨C,hC,hf,hF⟩ := t.bounded
  simp_rw [← integral_sub (t.each (hU _) _) (t.target (hU _))]
  apply Metric.tendsto_nhds.mpr; intro ε hε
  let c (i : ℕ) := (U i:M)
  letI : ∀ i, IsFiniteMeasure (c i) := fun i ↦ by dsimp [c]; infer_instance
  let M' := (μ.mass:ℝ) + 1
  have hp : 0 < M' := by dsimp [M']; positivity
  let e := ε / 2
  have hq : 0 < e := half_pos hε
  obtain ⟨n,H⟩ := smallClosedComplement h (e/(C+C)) (by positivity)
  let R := ball (0:E4) (n:ℝ)
  have hr : MeasurableSet R := isOpen_ball.measurableSet
  let K := closedBall (0:E4) (n:ℝ) ∩ positiveHalf
  have hk : IsCompact K := (isCompact_closedBall _ _).inter_right positiveHalf_closed
  have hm : Tendsto (fun i ↦ ((U i).mass:ℝ)) atTop (𝓝 (μ.mass:ℝ)) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp
      (FiniteMeasure.continuous_mass.continuousAt.tendsto.comp h)
  filter_upwards [H, hm.eventually (gt_mem_nhds (show (μ.mass:ℝ) < M' from lt_add_one _)),
    t.cost K inter_subset_right hk (e/M') (by positivity)] with i H w Y
  let u := c i
  letI : IsFiniteMeasure u := by dsimp [u]; infer_instance
  let g (x) := F i x - f x
  have hg : Integrable g u := (t.each (hU i) i).sub (t.target (hU i))
  let D := ∫ x in R, g x ∂u
  let D' := ∫ x in Rᶜ, g x ∂u
  have hd : ‖D‖ < e := by
    refine lt_of_le_of_lt (norm_setIntegral_le_of_norm_le_const_ae' (measure_lt_top u R)
      (Eventually.mono (hU i) (fun x p (y : x ∈ R) ↦ Y x ⟨ball_subset_closedBall y,p⟩))) ?_
    have hm : u.real R ≤ ((U i).mass:ℝ) := (show u.real R ≤ u.real univ from
      measureReal_mono (subset_univ _))
    calc e/M' * u.real R < e/M' * M' := mul_lt_mul_of_pos_left (hm.trans_lt w) (by positivity)
         _ = _ := by field_simp
  have hd' : ‖D'‖ < e := by
    have hx : ∀ᵐ x ∂u, x ∈ Rᶜ → ‖g x‖ ≤ C+C := Eventually.mono (hU i) fun x p _ ↦
      (norm_sub_le _ _).trans (add_le_add (hF _ x p) (hf x p))
    refine lt_of_le_of_lt (norm_setIntegral_le_of_norm_le_const_ae' (measure_lt_top u Rᶜ) hx) ?_
    calc _ < (C+C)*(e/(C+C)) := mul_lt_mul_of_pos_left H (by positivity)
         _ = _ := by field_simp
  change dist (∫ x, g x ∂u) 0 < _
  rw [dist_zero_right,← integral_add_compl hr hg]
  exact (norm_add_le D D').trans_lt ((add_lt_add hd hd').trans_eq (add_halves _))

/-- Moving test passage against varying finite narrow laws. -/
theorem zoomTestLimit (h : Tendsto U atTop (𝓝 μ)) (hU : ∀ i, Brilliant (U i))
    (hμ : Brilliant μ) (t : ZoomTest F f) :
    Tendsto (fun i ↦ ∫ x, F i x ∂(U i:M)) atTop (𝓝 (∫ x, f x ∂(μ:M))) := by
  have he := (diffLimit h hU t).add (targetLimit h hU hμ t)
  rw [zero_add] at he
  exact he.congr fun i ↦ sub_add_cancel _ _

end YM.Cheer.MatrixZoom
#print axioms YM.Cheer.MatrixZoom.zoomTestLimit

import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Weak convergence through varying bounded costs

Generic helper for the matrix zoom.
-/
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section

namespace YM.Six
open Function Filter Metric Set MeasureTheory
open scoped Topology ENNReal


variable {X : Type*} [MetricSpace X] [ProperSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]
  {ι : Type*} {l : Filter ι} {ν : FiniteMeasure X} {μ : ι → FiniteMeasure X}


/-- Eventual mass bound outside a compact. -/
lemma weak_tails (h : Tendsto μ l (𝓝 ν)) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Set X, IsCompact K ∧ ∀ᶠ i in l, ((μ i : Measure X).real Kᶜ) < ε := by
  obtain ⟨p⟩ := ‹Nonempty X›
  have ht : IsTightMeasureSet {(ν:Measure X)} := isTightMeasureSet_singleton
  obtain ⟨K,hK,hKμ⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp ht
    (ENNReal.ofReal (ε/2)) (by positivity)
  obtain ⟨r,hr⟩ := hK.isBounded.subset_ball p
  have hB : (ν:Measure X) (ball p r)ᶜ < ENNReal.ofReal ε := calc
    _ ≤ (ν : Measure X) Kᶜ := measure_mono (compl_subset_compl.mpr hr)
    _ ≤ _ := hKμ _ (mem_singleton _)
    _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr (half_lt_self hε)
  refine ⟨closedBall p r,isCompact_closedBall ..,?_⟩
  filter_upwards [eventually_lt_of_limsup_lt
    ((FiniteMeasure.limsup_measure_closed_le_of_tendsto h
      isOpen_ball.isClosed_compl).trans_lt hB)] with i hi
  exact (measureReal_mono (compl_subset_compl.mpr ball_subset_closedBall)).trans_lt
    (ENNReal.toReal_lt_of_lt_ofReal hi)

lemma weak_vary_zero (h : Tendsto μ l (𝓝 ν)) {F : ι → X → ℂ}
    (hb : ∃ C : ℝ, ∀ i x, ‖F i x‖ ≤ C)
    (hm : ∀ i, Measurable (F i))
    (hv : ∀ K, IsCompact K → TendstoUniformlyOn F 0 l K) :
    Tendsto (fun i => ∫ x, F i x ∂(μ i : Measure X)) l (𝓝 0) := by
  obtain ⟨c,hc⟩ := hb
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let C := max c 1
  have hC : ∀ i x, ‖F i x‖ ≤ C := fun i x => le_trans (hc i x) (le_max_left ..)
  have hC' : 0 < C := zero_lt_one.trans_le (le_max_right ..)
  let M := (ν:Measure X).real univ + 1
  have hM' : 0 < M := add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg zero_lt_one
  have hM : ∀ᶠ i in l, (μ i : Measure X).real univ < M := by
    have hB : (ν:Measure X) univ < ENNReal.ofReal M :=
      (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top _ _)).mpr (lt_add_one _)
    filter_upwards [eventually_lt_of_limsup_lt
      ((FiniteMeasure.limsup_measure_closed_le_of_tendsto h isClosed_univ).trans_lt hB)] with i hi
    exact ENNReal.toReal_lt_of_lt_ofReal hi
  obtain ⟨K,hK,hKμ⟩ := weak_tails h (ε/2/C) (by positivity)
  filter_upwards [hM,hKμ,Metric.tendstoUniformlyOn_iff.mp (hv K hK) (ε/2/M) (by positivity)]
    with i h1 h2 h3
  rw [dist_zero_right]
  have hfi : Integrable (F i) (μ i : Measure X) := Integrable.of_bound
    (hm i).aestronglyMeasurable C (ae_of_all _ (hC i))
  have hin (x) (hx : x ∈ K) : ‖F i x‖ ≤ ε/2/M := by simpa using (h3 x hx).le
  rw [← integral_add_compl hK.isClosed.measurableSet hfi]
  refine (norm_add_le _ _).trans_lt ((add_lt_add
    ((norm_setIntegral_le_of_norm_le_const (measure_lt_top (μ i : Measure X) _) hin).trans_lt
      (show _ < ε/2 from ?_))
    ((norm_setIntegral_le_of_norm_le_const (measure_lt_top (μ i : Measure X) _)
      (fun x (_:x ∈ Kᶜ) => hC i x)).trans_lt (show _ < ε/2 from ?_))).trans_eq (add_halves ε))
  · calc
      _ ≤ (ε/2/M) * (μ i : Measure X).real univ := by
        gcongr; exact measure_ne_top _ _; exact subset_univ _
      _ < (ε/2/M) * M := by gcongr
      _ = _ := by field_simp
  · exact (lt_div_iff₀' hC').mp h2

/-- Narrow convergence with variable costs uniformly bounded, uniformly
converging on each compact, continuous limit. -/
lemma weak_vary (h : Tendsto μ l (𝓝 ν)) {F : ι → X → ℂ} {f : X → ℂ}
    (hb : ∃ C : ℝ, ∀ i x, ‖F i x‖ ≤ C)
    (hb' : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hm : ∀ i, Measurable (F i)) (hf : Continuous f)
    (hv : ∀ K, IsCompact K → TendstoUniformlyOn F f l K) :
    Tendsto (fun i => ∫ x, F i x ∂(μ i : Measure X)) l
      (𝓝 (∫ x, f x ∂(ν:Measure X))) := by
  obtain ⟨a,A⟩ := hb; obtain ⟨b,B⟩ := hb'
  have hg : Tendsto (fun i => ∫ x, F i x - f x ∂(μ i : Measure X)) l (𝓝 0) := by
    refine weak_vary_zero (F:=fun i x => F i x-f x) h
      ⟨a+b, fun i x => (norm_sub_le _ _).trans (add_le_add (A i x) (B x))⟩
      (fun i => (hm i).sub hf.measurable)
      (fun K hk => Metric.tendstoUniformlyOn_iff.mpr fun e he => ?_)
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hv K hk) e he] with i hi x hx
    change dist 0 (F i x - f x) < _
    rw [dist_zero_left, ← dist_eq_norm, dist_comm]
    exact hi x hx
  have ht := hg.add ((FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp h
    (BoundedContinuousFunction.ofNormedAddCommGroup f hf b B))
  rw [zero_add] at ht
  exact ht.congr fun i => by
    have hg1 : Integrable (F i) (μ i : Measure X) := Integrable.of_bound
      (hm i).aestronglyMeasurable a (ae_of_all _ (A i))
    have hg2 : Integrable f (μ i : Measure X) := Integrable.of_bound
      hf.aestronglyMeasurable b (ae_of_all _ B)
    rw [integral_sub hg1 hg2]
    exact sub_add_cancel ..

end YM.Six

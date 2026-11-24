import Mathlib.MeasureTheory.Measure.Portmanteau
set_option autoImplicit false
open scoped Topology
noncomputable section
namespace MeasureTheory.FiniteMeasure
open Filter Set Metric
open scoped ENNReal NNReal Topology BoundedContinuousFunction
variable {X:Type*}[MetricSpace X][ProperSpace X][MeasurableSpace X][BorelSpace X]
variable {μ : ℕ→FiniteMeasure X}{ν:FiniteMeasure X}

-- Choose one compact ball to pay the family of all sufficiently late measures.
private lemma tail_ball [Nonempty X](h:Tendsto μ atTop (𝓝 ν)){ε:ℝ}(u:0<ε) :
    ∃ A:Set X, IsCompact A ∧ ∀ᶠ i:ℕ in atTop, ((μ i:Measure X)).real Aᶜ < ε := by
  let o:=Classical.arbitrary X
  let B(n:ℕ):=ball o n
  let U(n:ℕ):= (B n)ᶜ
  have he: ⋂ n:ℕ,U n=∅ := by
    ext x; simp only [mem_iInter, notMem_empty, iff_false]; intro p
    obtain ⟨n,w⟩:= exists_nat_gt (dist x o)
    exact p n (mem_ball.mpr w)
  have ht : Tendsto (fun n:ℕ=> (ν:Measure X) (U n)) atTop (𝓝 0):= by
    have hv : Antitone U:=fun m n p=> Set.compl_subset_compl.mpr (ball_subset_ball (by exact_mod_cast p))
    have hk:= tendsto_measure_iInter_atTop (μ:=(ν:Measure X)) (fun i:ℕ=> (show MeasurableSet (U i) from (isOpen_ball (x:=o) (ε:=(i:ℝ))).measurableSet.compl).nullMeasurableSet) hv (show ∃ i, (ν:Measure X) (U i)≠⊤ from ⟨0,measure_ne_top _ _⟩)
    rwa [he,measure_empty] at hk
  obtain ⟨i,p⟩ := (ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr u))).exists
  let A := Metric.closedBall o (i:ℝ)
  have hw:= FiniteMeasure.limsup_measure_closed_le_of_tendsto h (show IsClosed (U i) from isOpen_ball.isClosed_compl)
  refine ⟨A,isCompact_closedBall ..,?_⟩
  filter_upwards [eventually_lt_of_limsup_lt (hw.trans_lt p)] with n k
  exact ENNReal.toReal_lt_of_lt_ofReal ((measure_mono (Set.compl_subset_compl.mpr ball_subset_closedBall)).trans_lt k)

-- Useful for varying bounded continuous spectral tests.
theorem integral_moving_test [Nonempty X](h:Tendsto μ atTop (𝓝 ν))
    (g:ℕ→X→ᵇ ℂ)(f:X→ᵇ ℂ)(M:ℝ)(b:∀ i:ℕ,‖g i‖ ≤ M)
    (hg:∀ A:Set X,IsCompact A → TendstoUniformlyOn (fun i => g i) f atTop A) :
    Tendsto (fun i=> ∫ x, g i x ∂(μ i:Measure X)) atTop (𝓝 (∫ x, f x ∂(ν:Measure X))):= by
  let V(i):= g i-f
  have he : Tendsto (fun i=> ∫ x, V i x ∂(μ i:Measure X)) atTop (𝓝 0):= by
    rw [Metric.tendsto_nhds]
    intro ε e
    have hM:=le_trans (norm_nonneg (g 0)) (b 0)
    let C:=M+‖f‖+1
    have hc:0<C:=by unfold C; positivity
    let t:ℝ:= ε/3
    have ht:0<t:=by unfold t; positivity
    obtain ⟨A,u,p⟩:=tail_ball h (show 0<t/C from by positivity)
    let D:ℝ := (ν.mass:ℝ)+1
    have hD:0<D:=by unfold D; positivity
    have h':Tendsto (fun i=> ((μ i).mass:ℝ)) atTop (𝓝 (ν.mass:ℝ)):=tendsto_subtype_rng.mp h.mass
    filter_upwards [p, h'.eventually (ge_mem_nhds (lt_add_one _)), Metric.tendstoUniformlyOn_iff.mp (hg A u) (t/D) (by positivity)] with i w r l
    have h₁ : ‖∫ x in A, V i x ∂(μ i:Measure X)‖≤ t:= by
      apply le_trans (norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) (f:= fun x=> V i x) (C:=t/D) ?_) ?_
      · intro x k
        simpa [V,← dist_eq_norm,dist_comm] using (l x k).le
      calc _ ≤ (t/D)*D := by
                    gcongr
                    exact (measureReal_mono (μ:=(μ i:Measure X)) (subset_univ A)).trans r
           _ = t := by field_simp
    have h₂ : ‖∫ x in Aᶜ, V i x ∂(μ i:Measure X)‖≤ t:= by
      apply le_trans (norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) (f:=fun x=> V i x) (C:=C) ?_) ?_
      · intro x k
        exact ((V i).norm_coe_le_norm x).trans ((norm_sub_le (g i) f).trans ((add_le_add_left (b i) ‖f‖).trans ((lt_add_one _).le))) -- tune args
      calc _ ≤ C*(t/C):= by gcongr
           _ = t:= by field_simp
    rw [dist_zero_right, ← integral_add_compl u.measurableSet ((V i).integrable _)]
    apply (norm_add_le ..).trans_lt
    unfold t at *
    linarith
  have hw:=he.add ((FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp h f)
  rw [zero_add] at hw
  exact hw.congr fun i=> by
    change (∫ x, (g i x - f x) ∂(μ i:Measure X))+ _ = _
    rw [integral_sub ((g i).integrable _) (f.integrable _),sub_add_cancel]
end MeasureTheory.FiniteMeasure

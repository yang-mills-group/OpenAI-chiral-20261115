import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.MeasureTheory.Function.L2Space

/-!
# SatinThinInteraction -- payment helper

Optional, independent from (not used as input by) the written proof. For one central
porting step. Use Lp ℝ; no restriction to the positive frequency half-line since we want
ONE prescription including the conjugate prices. Use `ProbabilityTheory.complexMGF` on
positive measures, applying near-zero identity criterion only.
-/

noncomputable section
namespace YM.SatinThin
open scoped Topology ENNReal NNReal MeasureTheory ProbabilityTheory Real InnerProductSpace
open MeasureTheory Filter Set TopologicalSpace ProbabilityTheory

section laplace
variable {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {h : ℝ}

/-- Near-zero (even just on a dense subset) mgf test. -/
lemma finite_measure_eq {T : Set ℝ} (ht : Dense T) (hp : 0 < h)
    (hm : Ioo (-h) h ⊆ integrableExpSet id μ) (hn : Ioo (-h) h ⊆ integrableExpSet id ν)
    (he : EqOn (mgf id μ) (mgf id ν) (Ioo (-h) h ∩ T)) : μ=ν := by
  let U := {z : ℂ | z.re ∈ Ioo (-h) h}
  have h1 : AnalyticOnNhd ℂ (complexMGF id μ) U :=
    analyticOnNhd_complexMGF.mono (fun _ hz => interior_maximal hm isOpen_Ioo hz)
  have h2 : AnalyticOnNhd ℂ (complexMGF id ν) U :=
    analyticOnNhd_complexMGF.mono (fun _ hz => interior_maximal hn isOpen_Ioo hz)
  have hopen : (0:ℝ) ∈ Ioo (-h) h := ⟨by linarith,hp⟩
  have hc := mem_closure_iff_frequently.mp
    ((dense_compl_singleton (0:ℝ)).inter_of_isOpen_left ht (isClosed_singleton.isOpen_compl) 0)
  have h3 : EqOn (complexMGF id μ) (complexMGF id ν) U := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq h1 h2
      ((convex_Ioo (-h) h).linear_preimage Complex.reLm).isPreconnected
      (z₀:=((0:ℝ):ℂ)) (by change (_:ℝ) ∈ Ioo (-h) h; simpa using hopen) ?_
    have hh : ∃ᶠ (x:ℝ) in 𝓝[≠] (0:ℝ), complexMGF id μ (x:ℂ)=complexMGF id ν (x:ℂ) := by
      apply frequently_nhdsWithin_iff.mpr
      apply (hc.and_eventually (isOpen_Ioo.eventually_mem hopen)).mono
      rintro t ⟨ht, h⟩
      exact ⟨by
        rw [complexMGF_ofReal,complexMGF_ofReal,he (show t∈_ from ⟨h,ht.2⟩)], ht.1⟩
    rw [frequently_iff_seq_forall] at hh ⊢
    obtain ⟨xs, hx, hv⟩ := hh
    refine ⟨fun i => (xs i:ℂ), ?_, hv⟩
    rw [tendsto_nhdsWithin_iff] at hx ⊢
    exact ⟨tendsto_ofReal_iff.mpr hx.1, by simpa using hx.2⟩
  apply Measure.ext_of_charFun
  funext t
  rw [←complexMGF_id_mul_I, ←complexMGF_id_mul_I]
  exact h3 (by change (_:ℝ)∈ Ioo _ _; simpa using hopen)
end laplace

section stones
variable {μ : Measure ℝ} {h t : ℝ}
/-- Stones of the bilateral filter, in t=-d parameters. -/
def stone (h t x : ℝ) := Real.exp (-h*|x|+t*x)
lemma stone_bound (p : t ∈ Ioo (-h) h) (x : ℝ) : ‖stone h t x‖ ≤ 1 := by
  have ht : t ≤ h := p.2.le
  have hh : -h ≤ t := p.1.le
  unfold stone; rw [Real.norm_of_nonneg (Real.exp_nonneg _), Real.exp_le_one_iff]; rcases le_total 0 x with he | he
  · rw [abs_of_nonneg he]; nlinarith
  rw [abs_of_nonpos he]; nlinarith
lemma stone_meas (h t:ℝ) : AEStronglyMeasurable (stone h t) μ :=
  (show Continuous (stone h t) from by unfold stone; fun_prop).aestronglyMeasurable
lemma stone_int {b:ℝ → ℝ} (hi:Integrable b μ) (p : t ∈ Ioo (-h) h):
    Integrable (fun x => b x * stone h t x) μ :=
  hi.mul_bdd (stone_meas h t) (ae_of_all _ (stone_bound p))

private def blanket (h:ℝ) (b:ℝ → ℝ) (x:ℝ) := ENNReal.ofReal (b x * Real.exp (-h*|x|))
private lemma blanket_meas (h:ℝ) {b:ℝ → ℝ} (hi:Integrable b μ): AEMeasurable (blanket h b) μ :=
  (hi.aemeasurable.mul (show AEMeasurable (fun x:ℝ=> Real.exp (-h*|x|)) μ from by fun_prop)).ennreal_ofReal
private lemma heat_blanket (h t:ℝ) {b:ℝ → ℝ} (he: ∀ x, 0≤b x) (x:ℝ):
    (blanket h b x).toReal • Real.exp (t*x) = b x * stone h t x := by
  simp only [blanket, stone, ENNReal.toReal_ofReal (mul_nonneg (he x) (Real.exp_nonneg _)), Real.exp_add]
  rw [smul_eq_mul,mul_assoc]
private lemma blanketAll (h:ℝ) {b:ℝ → ℝ} (he: ∀ x, 0≤b x) (hi:Integrable b μ) :
    Ioo (-h) h ⊆ integrableExpSet id (μ.withDensity (blanket h b)) := by
  intro t p; change Integrable (fun x:ℝ => Real.exp (t*x)) _
  rw [integrable_withDensity_iff_integrable_smul₀' (blanket_meas h hi) (ae_of_all _ fun x=> by simp [blanket])]
  simp_rw [heat_blanket h t he]; exact stone_int hi p
private lemma finite_blanket (hp : 0<h) {b:ℝ → ℝ} (he: ∀ x, 0≤b x) (hi:Integrable b μ) :
    IsFiniteMeasure (μ.withDensity (blanket h b)) := by
  have h0 : (0:ℝ) ∈ _ := blanketAll h he hi (show 0 ∈ Ioo (-h) h from ⟨by linarith,hp⟩)
  apply (integrable_const_iff_isFiniteMeasure (c:=(1:ℝ)) one_ne_zero).mp
  simpa only [integrableExpSet,mem_setOf_eq,zero_mul,Real.exp_zero] using h0
private lemma blanketPrice (h t:ℝ) {b:ℝ → ℝ} (he: ∀ x, 0≤b x) (hi:Integrable b μ) :
    mgf id (μ.withDensity (blanket h b)) t = ∫ x, b x * stone h t x ∂μ:= by
  simp only [mgf, id]
  rw [integral_withDensity_eq_integral_toReal_smul₀ (blanket_meas h hi) (ae_of_all _ fun x=> by simp [blanket])]; simp_rw [heat_blanket h t he]
end stones

section budget
variable {μ : Measure ℝ} [IsFiniteMeasure μ] {h : ℝ}
lemma laplace_unique {T : Set ℝ} (ht : Dense T) (hp : 0<h) {a : ℝ → ℝ} (ha : Integrable a μ)
    (he : ∀ t ∈ Ioo (-h) h ∩ T, ∫ x, a x * stone h t x ∂μ = 0) : a =ᵐ[μ] 0 := by
  let f x := max (a x) 0
  let g (x:ℝ) := max (-a x) 0
  have hdecomp x : a x = f x - g x := by
    unfold f g; rcases le_total (a x) 0 with t|t
    · rw [max_eq_right t,max_eq_left (neg_nonneg.mpr t)]; simp
    rw [max_eq_left t,max_eq_right (neg_nonpos.mpr t)]; simp
  let p := μ.withDensity (blanket h f); let m := μ.withDensity (blanket h g)
  have hp' x : 0 ≤ f x := le_max_right _ _
  have hm' x : 0 ≤ g x := le_max_right _ _
  haveI : IsFiniteMeasure p := finite_blanket hp hp' ha.pos_part
  haveI : IsFiniteMeasure m := finite_blanket hp hm' ha.neg_part
  have hw : p=m := by
    refine finite_measure_eq ht hp (blanketAll h hp' ha.pos_part)
      (blanketAll h hm' ha.neg_part) (fun t ht => ?_)
    rw [blanketPrice h t hp' ha.pos_part, blanketPrice h t hm' ha.neg_part]
    apply sub_eq_zero.mp
    rw [←integral_sub (stone_int ha.pos_part ht.1) (stone_int ha.neg_part ht.1)]
    refine Eq.trans ?_ (he t ht)
    apply integral_congr_ae; filter_upwards with x; rw [← sub_mul, ← hdecomp x]
  have hx : blanket h f =ᵐ[μ] blanket h g := (withDensity_eq_iff_of_sigmaFinite
    (blanket_meas h ha.pos_part) (blanket_meas h ha.neg_part)).1 hw
  filter_upwards [hx] with x t
  have ht := mul_right_cancel₀ (Real.exp_pos (-h*|x|)).ne'
    ((ENNReal.ofReal_eq_ofReal_iff (mul_nonneg (hp' x) (Real.exp_nonneg _))
       (mul_nonneg (hm' x) (Real.exp_nonneg _))).mp t)
  rw [hdecomp, ht]; simp

/-- Subtype of allowed parameters. -/
abbrev Shop (T : Set ℝ) (h : ℝ) := ↥(Ioo (-h) h ∩ T)
lemma stone_mem2 (μ : Measure ℝ) [IsFiniteMeasure μ] {T : Set ℝ} (t : Shop T h) :
    MemLp (stone h t) 2 μ := MemLp.of_bound (stone_meas ..) 1 (ae_of_all _ (stone_bound t.prop.1))

/-- Bundled bilateral Laplace probe. -/
noncomputable def stone2 (μ : Measure ℝ) [IsFiniteMeasure μ] (T : Set ℝ) (h : ℝ)
    (t : Shop T h) : Lp ℝ 2 μ := (stone_mem2 μ t).toLp (stone h t)

lemma stone_span (μ : Measure ℝ) [IsFiniteMeasure μ] {T : Set ℝ} (ht : Dense T)
    (hp : 0<h) : (Submodule.span ℝ (Set.range (stone2 μ T h))).topologicalClosure=⊤ := by
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  refine le_antisymm (fun a ha => (Submodule.mem_bot ℝ).mpr (Lp.ext ?_)) bot_le
  refine EventuallyEq.trans (g:=0) (laplace_unique ht hp
    (MemLp.integrable (by norm_num) (Lp.memLp a)) (fun t e => ?_)) (Lp.coeFn_zero ..).symm
  let z : Shop T h := ⟨t,e⟩
  let x := stone2 μ T h z
  have hx := Submodule.subset_span (R:=ℝ) (mem_range_self (i:=z) (f:=stone2 μ T h))
  have H : inner ℝ x a=0 := Submodule.inner_right_of_mem_orthogonal hx ha
  rw [L2.inner_def] at H; rw [←H]; apply integral_congr_ae
  filter_upwards [(stone_mem2 μ z).coeFn_toLp] with i u
  change x i = stone h t i at u
  simp [u]

/-- Port of the bilateral approximation step: arbitrarily-small tolerance, requiring
only finiteness of measure (and can take the exact stamp mesh subset of reals). -/
lemma stone_purchase (μ : Measure ℝ) [IsFiniteMeasure μ] {T : Set ℝ} (ht : Dense T)
    (hp : 0 < h) (x : Lp ℝ 2 μ) {ε : ℝ} (p : 0<ε) : ∃ d : Shop T h →₀ ℝ,
    ‖x-∑ i∈d.support, d i • stone2 μ T h i‖ < ε := by
  let S := Submodule.span ℝ (range (stone2 μ T h))
  have hx : x ∈ S.topologicalClosure := (stone_span μ ht hp).symm ▸ Submodule.mem_top
  obtain ⟨y,q,e⟩ := Metric.mem_closure_iff.mp (show x∈ closure (S:Set ↑(Lp ℝ 2 μ)) from hx) ε p
  obtain ⟨d,rfl⟩ := (show y ∈ LinearMap.range (Finsupp.linearCombination ℝ (stone2 μ T h)) from (Finsupp.range_linearCombination ℝ (v:=stone2 μ T h)).symm ▸ q)
  exact ⟨d, lt_of_eq_of_lt (dist_eq_norm ..).symm e⟩
end budget
end YM.SatinThin
#print axioms YM.SatinThin.stone_purchase

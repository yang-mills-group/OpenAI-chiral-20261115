import YM.CF.Vp929.Analysis.LogSlit
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

set_option autoImplicit false
noncomputable section
namespace YM.CF.VolumeRate
open Complex Filter Topology Metric Set Function MeasureTheory
open scoped NNReal ENNReal BoundedContinuousFunction

/-- Compact extraction on one disk suffices. -/
lemma normal_subseq {ι : Type*} [Countable ι] {r R : ℝ} (hr : r < R)
    (f : ι → ℕ → ℂ → ℂ) (M : ι → ℝ) (hM : ∀ i, 0 ≤ M i)
    (h : ∀ i, ∀ᶠ n in atTop, DifferentiableOn ℂ (f i n) (ball 0 R) ∧ ∀ z ∈ ball (0:ℂ) R, ‖f i n z‖ ≤ M i) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, ∃ g : ℂ → ℂ, TendstoUniformlyOn (f i ∘ φ) g atTop (closedBall 0 r) ∧
      DifferentiableOn ℂ g (ball 0 r) ∧ ∀ z ∈ closedBall (0:ℂ) r, ‖g z‖ ≤ M i := by
  classical
  let B:=closedBall (0:ℂ) r; let U:=ball (0:ℂ) R; have H : B ⊆ U := closedBall_subset_ball hr
  let a := (R-r)/2; have ha : 0 < a := by dsimp [a]; linarith
  choose N hN using fun i=> eventually_atTop.mp (h i)
  let F (i:ι) (n:ℕ) := f i (max (N i) n)
  have hp i n := hN i (max (N i) n) (le_max_left ..)
  let Y (i : ι) : ℝ≥0 := ⟨M i/a, div_nonneg (hM _) ha.le⟩
  have hY i n : LipschitzOnWith (Y i) (F i n) B := by
    refine (convex_closedBall 0 r).lipschitzOnWith_of_nnnorm_deriv_le
              (fun x hx=> (hp i n).1.differentiableAt (isOpen_ball.mem_nhds (H hx))) ?_
    intro z hz
    have ht : closedBall z a ⊆ U := fun x he => mem_ball.mpr (lt_of_le_of_lt (dist_triangle x z 0) <|
       lt_of_le_of_lt (add_le_add (mem_closedBall.mp he) (mem_closedBall.mp hz)) (by unfold a; linarith))
    apply NNReal.coe_le_coe.mp; change ‖deriv _ _‖ ≤ _
    rw [← Complex.cderiv_eq_deriv isOpen_ball (hp i n).1 ha ht]; exact Complex.norm_cderiv_le ha fun x h => (hp i n).2 _ (ht (sphere_subset_closedBall h))
  let G (i) (n) : B →ᵇ ℂ := BoundedContinuousFunction.mkOfCompact ⟨B.restrict (F i n), continuousOn_iff_continuous_restrict.mp (((hp i n).1.mono H).continuousOn)⟩
  have ht (i : ι) : IsCompact (closure (range (G i))) := by
    refine BoundedContinuousFunction.arzela_ascoli (closedBall 0 (M i)) (isCompact_closedBall ..) _ (fun f x ⟨n,e⟩=> by subst f; exact mem_closedBall_zero_iff.mpr ((hp i n).2 _ (H x.prop)))
      (LipschitzWith.uniformEquicontinuous _ (Y i) ?_).equicontinuous
    rintro ⟨g,n,e⟩; subst g; exact lipschitzOnWith_iff_restrict.mp (hY i n)
  let W (n:ℕ) (i:ι):=G i n
  obtain ⟨w,hW,φ,q,hφ⟩:= (isCompact_univ_pi ht).tendsto_subseq (x:=W)
        fun n i _ => subset_closure (mem_range_self n)
  refine ⟨φ,q,fun i => ?_⟩
  let g:=extend ((↑) : B → ℂ) (fun x=>(w i) x) 0
  have hf' : TendstoUniformlyOn (F i ∘ φ) g atTop B := by
    rw [tendstoUniformlyOn_iff_restrict, show B.restrict g = fun x=>(w i) x from
      funext (fun _ => Subtype.val_injective.extend_apply ..)]
    exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp (tendsto_pi_nhds.mp hφ i)
  have hf : TendstoUniformlyOn (f i ∘ φ) g atTop B := hf'.congr <| by
    filter_upwards [q.tendsto_atTop (eventually_ge_atTop (N i))] with n hn
    change N i ≤ φ n at hn
    dsimp [EqOn,F]; rw [max_eq_right hn]; tauto
  have H' := q.tendsto_atTop.eventually (h i)
  refine ⟨g,hf,(hf.tendstoLocallyUniformlyOn.mono ball_subset_closedBall).differentiableOn (?_) isOpen_ball,
    fun z hz=> le_of_tendsto ((hf.tendsto_at hz).norm) (H'.mono fun n A=> A.2 _ (H hz))⟩
  exact H'.mono fun n A=> A.1.mono (ball_subset_closedBall.trans H)

/-- A.e. liminf argument. -/
private lemma pay_liminf (f : ℕ → ℝ → ℝ) (M : ℝ) (μ : Measure ℝ)
    (h : ∀ n, Integrable (f n) μ) (p : ∀ n, (∀ᵐ x ∂μ, 0 ≤ f n x) ∧ (∫ x, f n x ∂μ) ≤ M) :
    ∀ᵐ x ∂μ, ∃ C : ℝ, 0 ≤ C ∧ ∃ᶠ n in atTop, f n x < C := by
  let g (n:ℕ) := fun x => ENNReal.ofReal (f n x); have hg n : AEMeasurable (g n) μ :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable (h n).aemeasurable
  let L (x) := liminf (fun n=> g n x) atTop
  have hm : AEMeasurable L μ := by
    unfold L; simp_rw [liminf_eq_iSup_iInf_of_nat']; exact .iSup fun n=> .iInf fun i => hg _
  have hi (n) : ∫⁻ x, g n x ∂μ ≤ ENNReal.ofReal M := by unfold g; rw [← ofReal_integral_eq_lintegral_ofReal (h n) (p n).1]; exact ENNReal.ofReal_le_ofReal (p n).2
  have hv : ∫⁻ x, L x ∂μ < ⊤ := (le_trans (lintegral_liminf_le' (ι:=ℕ) (u:=atTop) (fun n=>hg n))
              (liminf_le_of_frequently_le' (Frequently.of_forall hi))).trans_lt ENNReal.ofReal_lt_top
  filter_upwards [ae_lt_top' hm hv.ne] with x hx; obtain ⟨n,p⟩ := ENNReal.exists_nat_gt hx.ne
  refine ⟨n,by positivity, ((frequently_lt_of_liminf_lt) p).mono ?_⟩
  intro k hk; rw [← ENNReal.ofReal_natCast] at hk; exact (ENNReal.ofReal_lt_ofReal_iff'.mp hk).1

/-- Almost every scaled pivot works for the auxiliary records on infinitely many of the periods;
`φ` is common to all periods. The `Eventually` over cutoffs is inside the period quantifier. -/
theorem paid_points (V : ℕ → ℝ) (hv : ∀ i, 1 ≤ V i) (M a : ℝ) (F : ℕ → ℕ → ℂ → ℂ)
    (h : ∀ i, ∀ᶠ n in atTop, DifferentiableOn ℂ (F i n) (ball 0 1) ∧
      (∀ z ∈ ball (0:ℂ) 1, ‖F i n z‖ ≤ Real.exp (M*V i)) ∧
      ∃ x : ℝ, |x| ≤ 1/8 ∧ Real.exp (a*V i) ≤ ‖F i n x‖) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ x : ℝ ∂choiceMeasure, ∃ C : ℝ, ∃ᶠ i in atTop, ∀ᶠ n in atTop,
                           Real.exp (C*V i) / 2 ≤ ‖F i (φ n) x‖ := by
  classical
  obtain ⟨φ,hφ,G⟩ := normal_subseq (r:= 9/10) (by norm_num) F (fun i=>Real.exp (M*V i)) (fun i=>(Real.exp_pos _).le)
    (fun i => (h i).mono (fun n h=> ⟨h.1,h.2.1⟩))
  choose g t hd hg using G
  refine ⟨φ,hφ,?_⟩
  have hb (x : ℝ) (hx : |x| ≤ 1/8) : (x:ℂ) ∈ ball (0:ℂ) (9/10) := mem_ball_zero_iff.mpr <| by rw [norm_real,Real.norm_eq_abs]; linarith
  let A (i : ℕ) := Real.exp (a*V i)
  have B (i : ℕ) : ∃ x : ℝ, |x| ≤ 1/8 ∧ A i ≤ ‖g i x‖ := by
    let K:=Icc (- (1/8:ℝ)) (1/8); have He (z) : z∈K ↔ |z| ≤ 1/8 := abs_le.symm
    obtain ⟨x,hx,p⟩:= isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by norm_num))
                (show ContinuousOn (fun x:ℝ=> ‖g i x‖) K from ((hd i).continuousOn.comp
                  Complex.continuous_ofReal.continuousOn fun x hx=> hb _ ((He _).mp hx)).norm)
    refine ⟨x,(He _).mp hx, le_of_not_gt fun q => ?_⟩
    let b:= ‖g i x‖
    obtain ⟨n,p₁,z,hz,e⟩:= ((Metric.tendstoUniformlyOn_iff.mp (t i) (A i-b) (sub_pos.mpr q)).and
                 (hφ.tendsto_atTop.eventually ((h i).mono (fun _ A=> A.2.2)))).exists
    have hV : ‖g i z‖ ≤ b := p ((He _).mpr hz)
    have hU : ‖F i (φ n) z‖ - ‖g i z‖ < A i-b := lt_of_le_of_lt (norm_sub_norm_le ..) (by
      simpa only [comp_apply, ←dist_eq_norm, dist_comm (F i (φ n) z)] using p₁ (z:ℂ) (ball_subset_closedBall (hb z hz)))
    linarith only [e,hV,hU]
  let d (i) := loss (M*V i) (g i); let s := Real.log (3/2); have hs : 0 < s := Real.log_pos (by norm_num)
  have D (i) := show (∀ᵐ x : ℝ ∂choiceMeasure, g i x ≠ 0 ∧ 0 ≤ d i x) ∧ Integrable (d i) choiceMeasure ∧
      (∫ x, d i x ∂choiceMeasure) ≤ 4*((M*V i-a*V i)/s+1) from by
    obtain ⟨c,H,E⟩:= B i; have hQ : closedBall (c:ℂ) (3/4) ⊆ ball (0:ℂ) (9/10) := by
      refine fun x hx=> mem_ball.mpr (lt_of_le_of_lt (dist_triangle x (c:ℂ) 0) ?_)
      rw [dist_zero_right,norm_real,Real.norm_eq_abs]; linarith [mem_closedBall.mp hx]
    exact integral_loss H _ ((hd i).mono hQ) (fun z h => hg _ _ (ball_subset_closedBall (hQ h))) E
  have v i : 0 < V i := lt_of_lt_of_le zero_lt_one (hv _); let u := pay_liminf (fun i x=> d i x / V i) (4*((M-a)/s+1)) choiceMeasure
        (fun i => (D i).2.1.div_const _) (fun i=> ⟨(D i).1.mono fun x hx=> div_nonneg hx.2 (v i).le, by
            rw [integral_div]; apply (div_le_iff₀ (v i)).2; apply le_trans (D i).2.2; have := hv i; simp only [div_eq_mul_inv]; linarith⟩)
  filter_upwards [u,ae_all_iff.2 fun i=> (D i).1,ae_restrict_mem measurableSet_Ioc] with x hx p hp
  obtain ⟨C,-,H⟩:= hx; refine ⟨M-C,H.mono ?_⟩
  intro i e; have ha : Real.exp ((M-C)*V i) ≤ ‖g i x‖ := by
    have h : M*V i-Real.log ‖g i x‖ ≤ C*V i := (div_le_iff₀ (v i)).1 e.le
    conv_rhs => rw [←Real.exp_log (norm_pos_iff.mpr (p i).1)]
    apply Real.exp_monotone; linarith
  exact ((t i).tendsto_at (ball_subset_closedBall (hb x ((abs_of_pos hp.1).trans_le hp.2)))).norm.eventually
      (le_mem_nhds (lt_of_lt_of_le (by linarith [Real.exp_pos ((M-C)*V i)]) ha))
end YM.CF.VolumeRate

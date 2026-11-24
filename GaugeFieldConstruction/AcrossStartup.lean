/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Vale.Bob
/-!
# Action at the actual top and missing-mask price

PSD fact on the one-face fourth jet (no large volume assumption).
In particular we don't need to pay continuity prices on plaquettes just
beyond the current Month's cap.
-/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2800
namespace YM.SatinBatches
open Function Filter Metric Work Tensor Next.Fluctuations WilsonStartup
open scoped ContDiff Topology Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable (G : Gauge)

-- ball version of WilsonStartup.FlatAt.bound
private theorem uniform_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (q : ℕ) (f : E → F)
    (h : FlatAt q f 0) (hZ : ContDiffAt ℝ ω f 0) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ x in 𝓝 (0:E), ‖f x‖ ≤ c*‖x‖^q := by
  obtain ⟨ε,hε,he⟩ : ∃ ε > (0:ℝ), ∀ x ∈ Metric.closedBall (0:E) ε, ContDiffAt ℝ ω f x ∧
             ‖iteratedFDeriv ℝ q f x‖ ≤ ‖iteratedFDeriv ℝ q f 0‖+1 :=
    Metric.nhds_basis_closedBall.eventually_iff.mp ((hZ.eventually (by simp)).and (hZ.continuousAt_iteratedFDeriv (k:=q) le_top |>.norm |>.eventually <| ge_mem_nhds (by linarith)))
  let c:= ‖iteratedFDeriv ℝ q f 0‖+1; have hc: 0≤c:=by unfold c; positivity
  have H : ∀ j ≤ q, ∀ x ∈ Metric.closedBall (0:E) ε, ‖iteratedFDeriv ℝ j f x‖ ≤ c * ‖x‖^(q-j) := by
    intro j hj; induction hj using Nat.decreasingInduction with
    | self => intro x hx; simpa using (he x hx).2
    | of_succ k hk ih =>
      intro x hx
      have hs : Metric.closedBall (0:E) ‖x‖ ⊆ Metric.closedBall 0 ε := closedBall_subset_closedBall (by simpa using hx)
      let J := iteratedFDeriv ℝ k f
      have hm (y : E) (hy : y ∈ Metric.closedBall (0:E) ‖x‖) : ‖fderiv ℝ J y‖ ≤ c * ‖x‖ ^ (q-(k+1)) := calc
        _ = ‖iteratedFDeriv ℝ (k+1) f y‖ := by
          rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply, LinearIsometryEquiv.norm_map]
        _ ≤ c*‖y‖^(q-(k+1)) := ih y (hs hy)
        _ ≤ c*‖x‖^(q-(k+1)) := by gcongr; simpa using hy
      have he' := (convex_closedBall (0:E) ‖x‖).norm_image_sub_le_of_norm_fderiv_le
        (fun y u => (he y (hs u)).1.differentiableAt_iteratedFDeriv (by simp)) hm
        (x:=0) (y:=x) (by simp) (by simp)
      rw [show q-k = (q-(k+1))+1 by omega,pow_succ,← mul_assoc]
      simpa only [J,h k hk,sub_zero] using! he'
  exact ⟨c,hc,(show ∀ᶠ x : E in 𝓝 0, x∈closedBall 0 ε from closedBall_mem_nhds 0 hε).mono (fun x u=>by simpa using H 0 (Nat.zero_le _) x u)⟩

theorem fourth_nonneg (x : G.Color) : 0 ≤ Tensor.diagonal (fourth G) x := by
  let f:= inK G - Work.G05.blockTaylor 4 (inK G)
  obtain ⟨C,c,hE⟩:= uniform_bound 5 f
    (flat_sub_taylor _ 4 (inK_diff.of_le le_top)) (inK_diff.sub (Work.G05.blockTaylor_contDiff .. |>.contDiffAt))
  let q:= Tensor.diagonal (fourth G) x
  let s : Filter ℝ := 𝓝[>] 0
  have h : Tendsto (fun u:ℝ => u • x) s (𝓝 0) := by
    have e: ContinuousWithinAt (fun u:ℝ=> u • x) (Set.Ioi 0) 0:= (by fun_prop : Continuous _).continuousWithinAt
    simpa only [ContinuousWithinAt,zero_smul] using e
  change 0 ≤ q
  haveI : NeBot s:=inferInstanceAs (NeBot (𝓝[>] (0:ℝ)))
  have hz:Tendsto (fun t:ℝ=>q+C*t*‖x‖^5) s (𝓝 q):= by
    have hc: ContinuousWithinAt (fun t:ℝ=>q+C*t*‖x‖^5) (Set.Ioi 0) 0:= (by fun_prop : Continuous _).continuousWithinAt
    simpa only [ContinuousWithinAt,mul_zero,zero_mul,add_zero] using hc
  apply ge_of_tendsto hz
  filter_upwards [h.eventually hE,h.eventually (recover_right G),self_mem_nhdsWithin (a:= (0:ℝ)) (s:=Set.Ioi 0)] with t e u v
  change 0<t at v
  let y:=t • x
  let z:= recover G y
  have hv: G.curvature z=y:=u
  have hr:‖y‖^2 ≤ (G.chord z)^2:=pow_le_pow_left₀ (norm_nonneg _) (hv ▸ G.curvature_norm z) _
  have he:f y=G.price z-‖y‖^2/2-t^4*q:= by
    change inK G y- Work.G05.blockTaylor 4 (inK G) y = _
    rw [convert_taylor,show Tensor.diagonal (fourth G) y=_ from (Tensor.homogeneous _ x t)]
    change _ - (_+ t^4*q)=_; unfold inK z; ring
  change ‖f y‖ ≤ _ at e
  rw [Real.norm_eq_abs, norm_smul, Real.norm_of_nonneg v.le, he] at e
  have hp:0≤t^4*(q+C*t*‖x‖^5):= by nlinarith only [(abs_le.mp e).2,G.chord_price z,hr]
  exact nonneg_of_mul_nonneg_right hp (pow_pos v _)

open Lattice Wilson CF.Vale RG
variable (p : RG.Clip)
lemma dominated (hp:p.direct≤1)(x:G.El): p.direct*G.price x ≤ G.price x-Design.bulk p*surplus x:= by
  unfold surplus Design.bulk
  have h := mul_nonneg (sub_nonneg.mpr hp) ((div_nonneg (sq_nonneg ‖G.curvature x‖) (by norm_num : (0:ℝ)≤2)).trans (le_add_of_nonneg_right (fourth_nonneg G (G.curvature x))))
  linarith

local notation "S5"=> CF.SU.group
open Gauge CF CF.SU Finset
variable {n:Side}
lemma principal_lower (hp:p.direct≤1)(x : Config S5 n): p.direct*energy x ≤ Vale.ren p x:= by
  unfold Vale.ren energy WilsonStartup.residual
  rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _=>dominated _ p hp _)
lemma flag_energy (hp:p.direct≤1)(x:Config S5 n)(b:BudgetPoint)(hx: flags b.threshold x ≠ ∅):
 p.linear*b.threshold^2 ≤ basicP p x := by
  obtain ⟨i,v⟩:= nonempty_iff_ne_empty.mpr hx; obtain ⟨j,_,hj⟩:= (flags_spec ..).mp v
  have he : ((CF.SU.group).price (faceValue x j)) ≤ energy x:= Finset.single_le_sum (fun i _ => ((CF.SU.group).price_range _).1) (mem_univ j)
  have hb:= principal_lower p hp x; have hu:0≤energy (Reef.echo x):= Finset.sum_nonneg (fun i _ => ((CF.SU.group).price_range _).1)
  have hc:= (mul_nonneg p.quadratic_pos.le hu).trans (principal_lower p hp _)
  have hy: b.threshold^2/2 ≤energy x :=by nlinarith [pow_le_pow_left₀ b.threshold_pos.le hj.le 2,(CF.SU.group).chord_price (faceValue x j)]
  unfold basicP
  nlinarith only [hc,hb, mul_le_mul_of_nonneg_right (show p.linear ≤ p.direct/4 by linarith [p.kink,p.quadratic_pos]) (sq_nonneg b.threshold), mul_le_mul_of_nonneg_left hy p.quadratic_pos.le]

#print axioms fourth_nonneg
end YM.SatinBatches

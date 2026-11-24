import Mathlib
/-!
 # Complex Taylor bound on banach argument, from prices on a ball
 -/
noncomputable section
open Metric Set Filter
open scoped Topology NNReal ENNReal
namespace YM.Dally.Surf
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {f : E → F} {x : E} {R C d : ℝ}
omit [CompleteSpace F] in
private lemma cauchy_of_cost (hd : 0 < d) (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f (closedBall x d))
    (he : ∀ y ∈ closedBall x d, ‖f y‖ ≤ C) : ‖fderiv ℂ f x‖ ≤ C / d := by
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) ?_
  intro v hv
  let g (z : ℂ) := z • v + x
  have maps : MapsTo g (closedBall 0 d) (closedBall x d) := by
    intro z hz
    simpa [g, mem_closedBall, dist_eq_norm, norm_smul, hv] using hz
  have derg (z) : HasDerivAt g v z := by
    simpa [g] using (((hasDerivAt_id' z).smul_const v).add_const x)
  have H z (hz : z ∈ closedBall (0 : ℂ) d) : HasDerivAt (f ∘ g) (fderiv ℂ f (g z) v) z :=
    (hf _ (maps hz)).differentiableAt.hasFDerivAt.comp_hasDerivAt z (derg z)
  have A : DiffContOnCl ℂ (f ∘ g) (ball 0 d) := by
    refine ⟨fun z hz => ((H z (ball_subset_closedBall hz)).differentiableAt).differentiableWithinAt,
      fun z hz => (H z (closure_ball_subset_closedBall hz)).continuousAt.continuousWithinAt⟩
  have H' := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hd A fun y hy =>
    he _ (maps (sphere_subset_closedBall hy))
  rwa [(H 0 (mem_closedBall_self (le_of_lt hd))).deriv, show g 0 = _ from (by simp [g] : g 0 = x)] at H'

lemma extravaganza (hd : 0 < d) (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f (closedBall x R)) (he : ∀ y ∈ closedBall x R, ‖f y‖ ≤ C)
    (k : ℕ) : ∀ y ∈ closedBall x (R - k*d), ‖iteratedFDeriv ℂ k f y‖ ≤ C / d^k := by
  induction k with
  | zero => simpa [norm_iteratedFDeriv_zero] using he
  | succ k ih =>
    intro y hy
    have sub : closedBall y d ⊆ closedBall x (R - k*d) := by
      intro z hz
      have := dist_triangle z y x
      simp only [mem_closedBall, Nat.cast_add, Nat.cast_one] at *
      linarith
    have lt : closedBall x (R - k*d) ⊆ closedBall x R :=
      closedBall_subset_closedBall (sub_le_self _ (by positivity))
    rw [← norm_fderiv_iteratedFDeriv, pow_succ, ← div_div]
    exact cauchy_of_cost hd (by positivity) ((hf.iteratedFDeriv k).mono (sub.trans lt))
      fun z hz => ih z (sub hz)

def slipper (f : E → F) (x : E) : FormalMultilinearSeries ℂ E F :=
  fun k => (k.factorial : ℂ)⁻¹ • iteratedFDeriv ℂ k f x

lemma plush (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall x R))
    (he : ∀ y ∈ closedBall x R, ‖f y‖ ≤ C) (k : ℕ) :
    ‖slipper f x k‖ ≤ C * (Real.exp 1 / R)^k := by
  have hC := (norm_nonneg _).trans (he x (mem_closedBall_self hR.le))
  obtain h|h := k.eq_zero_or_pos
  · subst k
    simpa [slipper, norm_iteratedFDeriv_zero] using he x (mem_closedBall_self hR.le)
  have K : (0:ℝ) < k := by exact_mod_cast h
  have U := extravaganza (x := x) (d := R/k) (by positivity) hC hf he k x
    (mem_closedBall_self <| by
      apply sub_nonneg.mpr
      rw [mul_div_cancel₀ R (ne_of_gt K)]
      )
  have I : (k:ℝ)^k / k.factorial ≤ Real.exp 1^k := by
    rw [← Real.exp_nat_mul, mul_one]
    exact Real.pow_div_factorial_le_exp k K.le k
  calc
    _ = (k.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℂ k f x‖ := by simp [slipper, norm_smul]
    _ ≤ (k.factorial : ℝ)⁻¹ * (C / (R/k)^k) := by gcongr
    _ = (C/R^k) * ((k : ℝ)^k / k.factorial) := by rw [div_pow, div_div_eq_mul_div]; ring
    _ ≤ C/R^k * (Real.exp 1)^k := mul_le_mul_of_nonneg_left I (by positivity)
    _ = _ := by rw [div_pow]; ring

lemma poses (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall x R))
    (he : ∀ y ∈ closedBall x R, ‖f y‖ ≤ C) {r : ℝ≥0} (hr : (r:ℝ) = R / Real.exp 1) :
    HasFPowerSeriesOnBall f (slipper f x) x (r:ℝ≥0∞) := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  let p := slipper f x
  have RP : (0:ℝ≥0∞) < r := ENNReal.coe_pos.mpr (show 0 < r from by
    rw [← NNReal.coe_pos, hr]
    positivity)
  have LE : (r:ℝ≥0∞) ≤ p.radius := by
    apply p.le_radius_of_bound C
    intro n
    calc
      _ ≤ (C * (Real.exp 1 / R)^n) * (r:ℝ)^n := by gcongr; exact plush hR hf he _
      _ = _ := by rw [hr, mul_assoc, ← mul_pow, div_mul_div_cancel₀ hR.ne', div_self (Real.exp_pos _).ne', one_pow, mul_one]
  have L : HasFPowerSeriesOnBall (fun y => p.sum (y-x)) p x r := by
    simpa only [zero_add] using ((p.hasFPowerSeriesOnBall (lt_of_lt_of_le RP LE)).mono RP LE).comp_sub x
  refine L.congr ?_
  have K : AnalyticOnNhd ℂ f (eball x r) := by
    apply hf.mono
    rw [eball_coe]
    apply ball_subset_closedBall.trans (closedBall_subset_closedBall ?_)
    rw [hr, div_le_iff₀ (Real.exp_pos _)]
    exact le_mul_of_one_le_right hR.le (Real.one_le_exp (by norm_num))
  refine L.analyticOnNhd.eqOn_of_preconnected_of_eventuallyEq K (convex_eball _ _).isPreconnected
    (mem_eball_self RP) ?_
  obtain ⟨q,s,U⟩ := hf x (mem_closedBall_self hR.le)
  filter_upwards [eball_mem_nhds x U.r_pos] with z hz
  have T : z-x ∈ eball 0 s := mem_eball.mpr <| by
    rw [← sub_self x, edist_sub_right]
    exact mem_eball.mp hz
  have Z := (U.hasSum_iteratedFDeriv T).tsum_eq
  simp only [add_sub_cancel] at Z
  simpa [FormalMultilinearSeries.sum, p, slipper] using Z

lemma sparkle {α : Type*} (f : α → E → F) (u : α → ℝ)
    (hR : 0 < R) (hu : Summable u)
    (hf : ∀ i, AnalyticOnNhd ℂ (f i) (closedBall x R))
    (he : ∀ i y, y ∈ closedBall x R → ‖f i y‖ ≤ u i) {r : ℝ≥0} (hr : (r:ℝ) = R / Real.exp 1) :
    HasFPowerSeriesOnBall (fun y => ∑' i, f i y)
      (fun n => ∑' i, slipper (f i) x n) x (r:ℝ≥0∞) := by
  let p : FormalMultilinearSeries ℂ E F := fun n => ∑' i, slipper (f i) x n
  let c := Real.exp 1 / R
  have hc : 0 < c := by dsimp [c]; positivity
  have RP : (0:ℝ≥0∞) < r := ENNReal.coe_pos.mpr (show 0 < r from by
    rw [← NNReal.coe_pos, hr]; positivity)
  have dr : c * (r:ℝ) = 1 := by
    rw [hr]
    dsimp [c]
    field_simp
  have up (i) : 0 ≤ u i := (norm_nonneg _).trans (he i x <| mem_closedBall_self hR.le)
  have H i n : ‖slipper (f i) x n‖ ≤ u i * c^n := plush hR (hf i) (he i) _
  have J n : Summable fun i => ‖slipper (f i) x n‖ := Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun i => H i n) (hu.mul_right _)
  have LE : (r:ℝ≥0∞) ≤ p.radius := by
    apply p.le_radius_of_bound (∑' i, u i)
    intro n
    have t : ‖p n‖ ≤ (∑' i, u i)*c^n := by
      rw [← hu.tsum_mul_right]
      exact (norm_tsum_le_tsum_norm (J n)).trans ((J n).tsum_le_tsum (fun i => H i n) (hu.mul_right _))
    refine (mul_le_mul_of_nonneg_right t (by positivity : 0 ≤ (r:ℝ)^n)).trans (le_of_eq ?_)
    rw [mul_assoc, ← mul_pow, dr, one_pow, mul_one]
  refine ⟨LE, RP, fun {y} hy => ?_⟩
  have Qβ : ‖y‖ < (r:ℝ) := by simpa [eball_coe, mem_ball, dist_eq_norm] using hy
  have Q := (summable_geometric_of_lt_one (by positivity : 0 ≤ c*‖y‖)
    (by exact (mul_lt_mul_of_pos_left Qβ hc).trans_eq dr))
  let a (i : α) (n : ℕ) := slipper (f i) x n (fun _ => y)
  have HQ : Summable (Function.uncurry a) := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun ⟨i,n⟩ => ?_) (hu.mul_of_nonneg Q up (fun n => by change 0 ≤ (c * ‖y‖)^n; positivity))
    change ‖a i n‖ ≤ u i * (c * ‖y‖) ^ n
    calc
      _ ≤ ‖slipper (f i) x n‖ * (‖y‖^n) := by simpa [a] using (slipper (f i) x n).le_opNorm (fun _ => y)
      _ ≤ (u i*c^n)* (‖y‖^n) := mul_le_mul_of_nonneg_right (H _ _) (by positivity)
      _ = _ := by ring
  change HasSum (fun n => p n fun _ => y) (∑' i, f i (x+y))
  have HP : p.sum y = ∑' i, f i (x+y) := by
    calc
      _ = ∑' n, ∑' i, a i n := by
        unfold FormalMultilinearSeries.sum
        refine tsum_congr fun n => ?_
        exact (ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => E) F fun _ => y).map_tsum (J n).of_norm
      _ = ∑' i, ∑' n, a i n := HQ.tsum_comm
      _ = _ := tsum_congr fun i => ((poses hR (hf i) (he i) hr).hasSum hy).tsum_eq
  rw [← HP]
  exact p.hasSum (eball_subset_eball LE hy)

/-- Normal summability in a Banach argument. -/
lemma amber {α : Type*} (f : α → E → F) (u : α → ℝ)
    (hR : 0 < R) (hu : Summable u)
    (hf : ∀ i, AnalyticOnNhd ℂ (f i) (closedBall x R))
    (he : ∀ i y, y ∈ closedBall x R → ‖f i y‖ ≤ u i) :
    AnalyticAt ℂ (fun y => ∑' i, f i y) x :=
  (sparkle (r := ⟨_, by positivity⟩) f u hR hu hf he rfl).analyticAt
end YM.Dally.Surf

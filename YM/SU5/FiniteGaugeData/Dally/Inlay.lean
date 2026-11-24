import Mathlib
/-!
 # complexified Lagrange layout, counting in ℂ ball
 -/
noncomputable section
open Finset Polynomial
open scoped Topology NNReal ENNReal
namespace YM.Dally.Inlay
variable {n i : ℕ} {r : ℝ} {z : ℂ}

def pier (n : ℕ) := range (n+1)
@[simp] lemma pier_mem : i ∈ pier n ↔ i ≤ n := by simp [pier]
@[simp] lemma pier_card (n : ℕ) : (pier n).card = n+1 := card_range _
def joist (n : ℕ) (r : ℝ) (i : ℕ) := (r/n)*i
def nail (n : ℕ) (r : ℝ) (i : ℕ) := (joist n r i : ℂ)
lemma port (hi : i ∈ pier n) (hr : 0 < r) : |joist n r i| ≤ r := by
  simp only [joist, abs_of_nonneg (by positivity : 0 ≤ r / (n:ℝ) * (i:ℝ))]
  obtain h|h := n.eq_zero_or_pos
  · subst n
    simpa using hr.le
  have I := pier_mem.mp hi
  refine le_trans (b := (r/n)*(n:ℝ)) ?_ (by rw [div_mul_cancel₀]; positivity)
  gcongr
lemma inject (n) (hr : 0 < r) : Set.InjOn (nail n r) (pier n) := by
  obtain h|h := n.eq_zero_or_pos
  · subst n
    simp [pier]
  intro i hi j hj eq

  simpa [nail, joist, h.ne', hr.ne'] using eq

def capstan (n : ℕ) (r : ℝ) (i : ℕ) : Polynomial ℂ := Lagrange.basis (pier n) (nail n r) i
lemma capstan_degree (hr : 0 < r) (hi : i ∈ pier n) :
    (capstan n r i).degree = (n : WithBot ℕ) := by
  simp [capstan, Lagrange.degree_basis (inject n hr) hi]

private lemma denomin (hi : i ∈ pier n) :
    ∏ j ∈ (pier n).erase i, |(i:ℝ) - j| = i.factorial * ((n-i).factorial : ℝ) := by
  induction n with
  | zero =>
    simp only [pier_mem, Nat.le_zero] at hi
    subst i
    simp [pier]
  | succ n ih =>
    by_cases h : i ≤ n
    · have ne : n+1 ≠ i := by omega
      have A := ih (pier_mem.mpr h)
      have pt : (pier (n+1)).erase i = insert (n+1) ((pier n).erase i) := by
        ext k
        simp
        omega
      have B : |(i:ℝ) - (n+1)| = (n+1) - (i:ℝ) := by
        rw [abs_sub_comm, abs_of_nonneg]
        have : (i:ℝ) ≤ n := by exact_mod_cast h
        linarith
      rw [pt, prod_insert (by simp), Nat.cast_add_one, B, A, show n+1-i = (n-i)+1 from by omega,
        Nat.factorial_succ]
      push_cast [Nat.cast_sub h]
      ring
    · have := pier_mem.mp hi
      obtain rfl : i = n+1 := Nat.le_antisymm this (by omega)
      have top : (pier (n+1)).erase (n+1) = range (n+1) := by ext; simp; omega
      rw [top, Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one, ← Nat.descFactorial_self,
        Nat.descFactorial_eq_prod_range, Nat.cast_prod]
      refine prod_congr rfl (fun j hj => ?_)
      have I : j ≤ n+1 := (mem_range.mp hj).le
      rw [Nat.cast_sub I, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast I))]

private lemma play (j) (hr : 0 < r) :
    ‖nail n r i - nail n r j‖ = (r/n)*|(i:ℝ) - j| := by
  rw [nail, nail, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, joist, joist,
    ← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ r/(n:ℝ))]
lemma exhaust (hi : i ∈ pier n) (hr : 0 < r) (hz : ‖z‖ ≤ r) :
    ‖(capstan n r i).eval z‖ ≤ (4*Real.exp 1)^n := by
  obtain h|h := n.eq_zero_or_pos
  · subst n
    simp only [pier_mem, Nat.le_zero] at hi
    subst i
    simp [capstan, pier]
  let s := (pier n).erase i
  have size : s.card = n := by simp [s, card_erase_of_mem hi]
  have t : ‖(capstan n r i).eval z‖ = (∏ j ∈ s, ‖z - nail n r j‖) / ((r/n)^n *
      (i.factorial * ( (n-i).factorial : ℝ))) := by
    rw [capstan, Lagrange.basis, eval_prod, norm_prod]
    simp only [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X, norm_div,
      ← div_eq_inv_mul, play _ hr, prod_div_distrib, prod_mul_distrib, prod_const,
      show ((pier n).erase i).card = n from size, denomin hi, div_pow, s]
  have K : (0:ℝ) < n.choose i := by exact_mod_cast (Nat.choose_pos <| pier_mem.mp hi)
  have G := Nat.choose_mul_factorial_mul_factorial (pier_mem.mp hi)
  have V : (i.factorial * ((n-i).factorial : ℝ)) = n.factorial / (n.choose i : ℝ) := by
    rw [eq_div_iff (ne_of_gt K), mul_comm, ← mul_assoc]
    exact_mod_cast G
  calc
    _ ≤ (2*r)^n/((r/n)^n * (n.factorial / (n.choose i : ℝ))) := by
      rw [t, V]
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc
        _ ≤ ∏ _ ∈ s, (2*r) := by
          refine prod_le_prod (fun _ _ => norm_nonneg _) ?_
          intro j hj
          refine (norm_sub_le _ _).trans ?_
          have A := port (mem_of_mem_erase hj) hr
          rw [nail, Complex.norm_real, Real.norm_eq_abs]
          linarith
        _ = _ := by rw [prod_const, size]
    _ = 2^n * n.choose i * ((n:ℝ)^n / n.factorial) := by
      have : 0 < (n:ℝ) := by exact_mod_cast h
      rw [div_pow]
      field_simp
      ring
    _ ≤ 2^n * ( (2:ℝ)^n) * ((Real.exp 1)^n) := by
      have A : (n.choose i:ℝ) ≤ 2^n := by exact_mod_cast (Nat.choose_le_two_pow n i)
      have B : (n:ℝ)^n / n.factorial ≤ (Real.exp 1)^n := by
        rw [← Real.exp_nat_mul, mul_one]
        exact Real.pow_div_factorial_le_exp _ (by positivity) n
      gcongr
    _ = _ := by rw [← mul_pow, ← mul_pow]; norm_num

def pine : ℝ := 8 * Real.exp 1
lemma pine_le : 1 ≤ pine := by
  unfold pine
  nlinarith [Real.one_le_exp (show (0:ℝ) ≤ 1 by norm_num)]
lemma income (n) (hr : 0 < r) (hz : ‖z‖ ≤ r) :
    ∑ i ∈ pier n, ‖(capstan n r i).eval z‖ ≤ pine^n := by
  calc
    _ ≤ ∑ _ ∈ pier n, (4*Real.exp 1)^n := sum_le_sum fun _ hi => exhaust hi hr hz
    _ = (↑(n+1:ℕ):ℝ) * (4*Real.exp 1)^n := by rw [sum_const, nsmul_eq_mul, pier_card]
    _ ≤ 2^n * (4*Real.exp 1)^n := by
      have I : n+1 ≤ 2^n := Nat.lt_pow_self (by decide)
      have B : (↑(n+1:ℕ):ℝ) ≤ 2^n := by exact_mod_cast I
      gcongr
    _ = _ := by rw [← mul_pow, pine]; ring
open Metric
def buzz (n : ℕ) (r : ℝ) (z : ℂ) (u : ℕ → ℂ) : ℂ :=
  ∑ i ∈ pier n, u i * eval z (capstan n r i)
lemma buzz_congr (u v : ℕ → ℂ) (h : ∀ i ∈ pier n, u i = v i) :
    buzz n r z u = buzz n r z v := sum_congr rfl fun i hi => by rw [h i hi]
lemma buzz_sub (n : ℕ) (r : ℝ) (z : ℂ) (u v : ℕ → ℂ) :
    buzz n r z (fun i => u i - v i) = buzz n r z u - buzz n r z v := by
  simp only [buzz, sub_mul, sum_sub_distrib]
lemma buzz_scale (n : ℕ) (r : ℝ) (z k : ℂ) (u : ℕ → ℂ) :
    buzz n r z (fun i => k * u i) = k * buzz n r z u := by
  rw [buzz, buzz, mul_sum]; simp [mul_assoc]
lemma buzz_node (hr : 0 < r) (hi : i ∈ pier n) (u : ℕ → ℂ) :
    buzz n r (nail n r i) u = u i := by
  simpa [buzz, capstan, Lagrange.interpolate_apply, eval_finsetSum] using
    Lagrange.eval_interpolate_at_node u (inject n hr) hi
lemma buzz_pol (hr : 0 < r) (p : Polynomial ℂ) (hd : p.degree ≤ ↑n) :
    buzz n r z (fun i => eval (nail n r i) p) = p.eval z := by
  have t : p.degree < ↑(pier n).card := hd.trans_lt (by
    rw [pier_card]; exact_mod_cast Nat.lt_succ_self n)
  simpa [buzz, capstan, Lagrange.interpolate_apply, eval_finsetSum] using congrArg (eval z)
    (Lagrange.eq_interpolate (inject n hr) t).symm
lemma buzz_expense (hr : 0 < r) (hz : ‖z‖ ≤ r) (u : ℕ → ℂ) {B : ℝ} (hp : 0 ≤ B)
    (hb : ∀ i ∈ pier n, ‖u i‖ ≤ B) : ‖buzz n r z u‖ ≤ B * pine^n := by
  calc
    _ ≤ ∑ i ∈ pier n, ‖u i * eval z (capstan n r i)‖ := norm_sum_le _ _
    _ ≤ B * ∑ i ∈ pier n, ‖eval z (capstan n r i)‖ := by simp_rw [norm_mul, mul_sum]; gcongr; exact hb _ ‹_›
    _ ≤ _ := mul_le_mul_of_nonneg_left (income n hr hz) hp

/- Geometric tolerance scale for Taylor tail after part n inclusive. -/
def plume (K R r : ℝ) := K / (1 - r/R)
lemma plume_nn {R r K : ℝ} (hp : 0 ≤ K) (hr : 0 < r) (hl : r < R) : 0 ≤ plume K R r :=
  div_nonneg hp (sub_nonneg.mpr ((div_lt_one (hr.trans hl)).2 hl).le)
private lemma stage (n : ℕ) {f : ℂ → ℂ} {R K r : ℝ} (hr : 0 < r) (hl : r < R)
    (h : AnalyticOnNhd ℂ f (closedBall 0 R)) (hp : 0 ≤ K)
    (he : ∀ z ∈ closedBall (0 : ℂ) R, ‖f z‖ ≤ K) :
    ∃ p : Polynomial ℂ, p.degree ≤ (n : WithBot ℕ) ∧
      ∀ z, ‖z‖ ≤ r → ‖f z - p.eval z‖ ≤ plume K R r * (r/R)^n := by
  let A (i : ℕ) := iteratedDeriv i f 0 / (i.factorial : ℂ)
  have R' : 0 < R := hr.trans hl
  have hc : DiffContOnCl ℂ f (ball 0 R) :=
    ⟨h.differentiableOn.mono ball_subset_closedBall, h.continuousOn.mono closure_ball_subset_closedBall⟩
  let p : Polynomial ℂ := ∑ i ∈ pier n, C (A i)*X^i
  refine ⟨p, (degree_sum_le ..).trans (Finset.sup_le (fun i hi => (degree_C_mul_X_pow_le _ _).trans ?_)), ?_⟩
  · exact_mod_cast pier_mem.mp hi
  intro z hz
  have Z : z ∈ ball (0 : ℂ) R := by rw [mem_ball, dist_zero_right]; exact hz.trans_lt hl
  let u (i : ℕ) := A i * z^i
  have Q' : (∑ i ∈ range (n+1), u i) = p.eval z := by simp [p, u, pier, eval_finsetSum]
  have Q : HasSum u (f z) := by
    convert! Complex.hasSum_taylorSeries_on_ball hc.differentiableOn Z using 1
    ext1 i
    dsimp [u, A]
    simp only [sub_zero]; ring
  let t := r/R
  have D (i) : ‖u i‖ ≤ K*t^i := by
    have M := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le i R' hc
      fun z hz => he z (sphere_subset_closedBall hz)
    calc
      _ = ‖iteratedDeriv i f 0‖ / i.factorial * ‖z‖^i := by simp [u, A]
      _ ≤ (i.factorial * K / R^i) / i.factorial * r^i := by gcongr
      _ = K*t^i := by dsimp [t]; rw [div_pow]; field_simp
  have t0 : 0 ≤ t := by dsimp [t]; positivity
  have t1 : t < 1 := (div_lt_one R').mpr hl
  let v (i : ℕ) := K * t^n * t^i
  have SE : Summable v := (summable_geometric_of_lt_one t0 t1).mul_left _
  have ST (i : ℕ) : ‖u (i + (n+1))‖ ≤ v i := by
    refine (D _).trans ?_
    calc
      _ ≤ K*t^(n+i) := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one t0 t1.le (by omega)) hp
      _ = _ := by rw [pow_add]; dsimp [v]; ring
  rw [← Q.tsum_eq, ← Q.summable.sum_add_tsum_nat_add (n+1), Q', add_sub_cancel_left]
  calc
    _ ≤ ∑' i, v i := by
      have V := SE.of_nonneg_of_le (fun _ => norm_nonneg _) ST
      exact (norm_tsum_le_tsum_norm V).trans (V.tsum_le_tsum ST SE)
    _ = _ := by
      dsimp [v]
      rw [tsum_mul_left, tsum_geometric_of_lt_one t0 t1]
      unfold plume
      dsimp [t]
      ring
lemma hiss (n : ℕ) {f : ℂ → ℂ} {R K r : ℝ} (hr : 0 < r) (hl : r < R)
    (h : AnalyticOnNhd ℂ f (closedBall 0 R)) (hp : 0 ≤ K)
    (he : ∀ z ∈ closedBall (0 : ℂ) R, ‖f z‖ ≤ K)
    (hz : ‖z‖ ≤ r) :
    ‖buzz n r z (fun i => f (nail n r i)) - f z‖ ≤ 2*plume K R r * (pine*(r/R))^n := by
  obtain ⟨p, hd, T⟩ := stage n hr hl h hp he
  have H := buzz_expense (n := n) hr hz (fun i => f (nail n r i)-p.eval (nail n r i))
    (hp := mul_nonneg (plume_nn hp hr hl) (pow_nonneg (a := r/R) (by have := hr.trans hl; positivity) n))
    fun i hi => T _ (by simpa [nail] using port hi hr)
  rw [buzz_sub, buzz_pol hr p hd] at H
  have I : (1:ℝ) ≤ pine^n := one_le_pow₀ pine_le
  have J := plume_nn hp hr hl
  calc
    _ = ‖(buzz n r z _ - p.eval z) - (f z - p.eval z)‖ := by congr 1; exact (sub_sub_sub_cancel_right ..).symm
    _ ≤ _ := (norm_sub_le ..).trans (le_trans (add_le_add H (T z hz)) (calc
      _ ≤ plume K R r * (r / R)^n * pine^n + (plume K R r * (r/R)^n)*pine^n := by
        exact add_le_add le_rfl (le_mul_of_one_le_right (by have := hr.trans hl; positivity) I)
      _ = _ := by ring))
end YM.Dally.Inlay

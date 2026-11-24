import YM.Next.STATIONARY.OneLoop.MomentumIntegral

/-!
# Latitude filters

Used at internal lines / for the columns in a determinant. We will cut on
angle, in *one* of the four directions, at the reduced zone of a cycle.
Allowed external tests have zero momentum (in just that direction,
in that zone). This gives functoriality of compression, while removing
slabs (for positive cutoff) around poles. Via
Ward, we can use a transverse magnetic test.

No need to work through a sharp filter with complex methods. We will instead
use mesh-to-integral convergence via real-variable methods, accompanied
by regularity just of the integrands near the closed integration region.
-/
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix MeasureTheory
open scoped BigOperators ContDiff Topology ENNReal ComplexConjugate Matrix

/-- Distance from `u` to 2πℤ. -/
def wrapDist (u : ℝ) := Metric.infDist u (Set.range fun n : ℤ => (2 * Real.pi)*n)

section
variable {u : ℝ}

lemma wrapDist_nonneg (u : ℝ) : 0 ≤ wrapDist u := Metric.infDist_nonneg

lemma wrapDist_continuous : Continuous wrapDist :=
  Metric.continuous_infDist_pt _

lemma wrapDist_le (u : ℝ) (a : ℤ) : wrapDist u ≤ |u - 2 * Real.pi * a| :=
  Metric.infDist_le_dist_of_mem (by exact ⟨a, rfl⟩)

lemma wrapDist_lower {r : ℝ} (h : ∀ a : ℤ, r ≤ |u - 2 * Real.pi * a|) :
    r ≤ wrapDist u := by
  rw [wrapDist, Metric.le_infDist (Set.range_nonempty _)]
  rintro _ ⟨a, rfl⟩
  exact h a

lemma wrapDist_add (u : ℝ) (z : ℤ) :
    wrapDist (u + 2 * Real.pi * z) = wrapDist u := by
  apply le_antisymm
  · apply wrapDist_lower
    intro a
    exact (wrapDist_le _ (a + z)).trans_eq (by congr 1; push_cast; ring)
  apply wrapDist_lower
  intro a
  exact (wrapDist_le _ (a - z)).trans_eq (by congr 1; push_cast; ring)

lemma wrapDist_neg (u : ℝ) : wrapDist (-u) = wrapDist u := by
  have h (u) : wrapDist u ≤ wrapDist (-u) := by
    apply wrapDist_lower
    intro a
    refine (wrapDist_le u (-a)).trans_eq ?_
    conv_rhs => rw [← abs_neg]
    congr 1; push_cast; ring
  exact le_antisymm (by simpa using h (-u)) (h u)

lemma wrapDist_eq (h : |u| ≤ Real.pi) : wrapDist u = |u| := by
  apply le_antisymm
  · simpa using wrapDist_le u 0
  apply wrapDist_lower
  intro a
  rcases lt_trichotomy a 0 with hlt|rfl|hlt
  · have hneg : (a : ℝ) ≤ -1 := by exact_mod_cast (show a ≤ -1 by omega)
    have hs := mul_le_mul_of_nonneg_left hneg Real.pi_pos.le
    exact le_trans h (le_trans (by linarith [(abs_le.mp h).1]) (le_abs_self _))
  · simp
  have hpos : (1:ℝ) ≤ a := by exact_mod_cast (show (1:ℤ) ≤ a by omega)
  have hs := mul_le_mul_of_nonneg_left hpos Real.pi_pos.le
  exact le_trans h (le_trans (by linarith [(abs_le.mp h).2]) (neg_le_abs _))

lemma wrapDist_hits (u : ℝ) :
    ∃ a : ℤ, |u - 2 * Real.pi * a| = wrapDist u := by
  let a := ⌊(u + Real.pi)/(2*Real.pi)⌋
  refine ⟨a, ?_⟩
  have hs := wrapDist_add u (-a)
  simp only [Int.cast_neg, mul_neg, ← sub_eq_add_neg] at hs
  refine (wrapDist_eq ?_).symm.trans hs
  have ht : 0 < 2 * Real.pi := by positivity

  unfold a
  have hl := div_lt_iff₀ ht |>.mp (Int.lt_floor_add_one ((u + Real.pi) / (2*Real.pi)))
  have hu := le_div_iff₀ ht |>.mp (Int.floor_le ((u + Real.pi) / (2*Real.pi)))
  rw [abs_le]; constructor <;> linarith

lemma wrapDist_zero : wrapDist 0 = 0 := by
  exact le_antisymm (by simpa using wrapDist_le 0 0) (wrapDist_nonneg _)

lemma wrapDist_eq_zero : wrapDist u = 0 ↔ ∃ a : ℤ, u = 2 * Real.pi * a := by
  constructor
  · intro h
    obtain ⟨a, h₁⟩ := wrapDist_hits u
    exact ⟨a, sub_eq_zero.mp (abs_eq_zero.mp (h₁.trans h))⟩
  rintro ⟨a, rfl⟩
  simpa [wrapDist_zero] using wrapDist_add 0 a

lemma wrapDist_nat_mul_le (n : ℕ) (u : ℝ) :
    wrapDist ((n:ℝ) * u) ≤ n * wrapDist u := by
  obtain ⟨a, h⟩ := wrapDist_hits u
  refine (wrapDist_le _ ((n:ℤ) * a)).trans_eq ?_
  push_cast
  rw [← h]
  conv_rhs => rw [← Nat.abs_cast n, ← abs_mul]
  congr 1; ring
end

/-- Embedding the real zone in the complex frequency space of a symbol. -/
def tap (x : Gaia) : Momentum := axes (exileE x)
lemma tap_real (x : Gaia) : star (tap x) = tap x := axes_real _
lemma tap_angle (x : Gaia) (a : Axis) : (tap x a).re = x a := rfl
lemma tap_smooth : ContDiff ℝ ω tap := by
  suffices he : ContDiff ℝ ω exileE from axes_maps.comp he
  exact contDiff_pi.mpr fun i => show ContDiff ℝ ω (fun y : Gaia => y i) from by fun_prop

structure Latitude where
  /-- cycle of reduced zone, e.g. L. -/
  cycle : Side
  /-- IR cutoff in reduced radians. Negative = no cutoff. -/
  radius : ℝ

namespace Latitude
variable (D : Latitude) (p : Momentum)

def mark := wrapDist (D.cycle.val * (p 3).re)
def active : Prop := D.radius < D.mark p
def safe : Prop := D.radius ≤ D.mark p
def quiet : Prop := D.mark p = 0

instance decActive : Decidable (D.active p) := (inferInstance : Decidable (_ < _))

lemma mark_continuous : Continuous D.mark :=
  wrapDist_continuous.comp (continuous_const.mul
    (Complex.continuous_re.comp (continuous_apply _)))

lemma mark_neg : D.mark (-p) = D.mark p := by
  rw [mark, mark, Pi.neg_apply, Complex.neg_re, mul_neg, wrapDist_neg]

@[simp] lemma active_neg : D.active (-p) ↔ D.active p := by simp [active, mark_neg]
@[simp] lemma safe_neg : D.safe (-p) ↔ D.safe p := by simp [safe, mark_neg]
@[simp] lemma quiet_neg : D.quiet (-p) ↔ D.quiet p := by simp [quiet, mark_neg]

lemma mark_rolls {p q} (h : rolls p q) : D.mark p = D.mark q := by
  obtain ⟨z,rfl⟩ := h
  refine (wrapDist_add ((D.cycle.val:ℝ) * (p 3).re) ((D.cycle.val:ℤ) * z 3)).symm.trans ?_
  unfold mark; congr 1
  simp [reciprocal]; ring

lemma mark_nonneg : 0 ≤ D.mark p := wrapDist_nonneg _

lemma mark_add {q} (h : D.quiet q) : D.mark (p+q) = D.mark p := by
  rw [mark, Pi.add_apply, Complex.add_re, mul_add]
  obtain ⟨n, hn⟩ := wrapDist_eq_zero.mp h
  rw [hn]
  exact wrapDist_add ..

lemma active_add {q} (h : D.quiet q) : D.active (p + q) ↔ D.active p := by
  exact iff_of_eq <| congrArg (D.radius < ·) (D.mark_add p h)
lemma safe_add {q} (h : D.quiet q) : D.safe (p + q) ↔ D.safe p := by
  exact iff_of_eq <| congrArg (D.radius ≤ ·) (D.mark_add p h)

variable {D p} {q : Momentum}

lemma active.safe (h : D.active p) : D.safe p := h.le

lemma active.rolls (h : D.active p) (h₀ : rolls p q) : D.active q :=
  h.trans_eq (D.mark_rolls h₀)
lemma safe.rolls (h : D.safe p) (h₀ : rolls p q) : D.safe q :=
  h.trans_eq (D.mark_rolls h₀)
lemma quiet.rolls (h : D.quiet p) (h₀ : rolls p q) : D.quiet q :=
  (D.mark_rolls h₀).symm.trans h

lemma quiet.of_eq (h : p 3 = 0) (D : Latitude) : D.quiet p := by
  simp only [Latitude.quiet,mark,h,Complex.zero_re,mul_zero,wrapDist_zero]
lemma quiet.neg (h : D.quiet p) : D.quiet (-p) := (D.quiet_neg p).mpr h

lemma quiet.add (h : D.quiet p) (h' : D.quiet q) : D.quiet (p+q) :=
  (D.mark_add p h').trans h

variable (D)

@[simp] lemma quiet_zero : D.quiet 0 := quiet.of_eq rfl D

def full : Latitude := ⟨1,-1⟩
@[simp] lemma full_active (p) : full.active p := lt_of_lt_of_le (by norm_num [full]) (full.mark_nonneg p)
@[simp] lemma full_safe (p) : full.safe p := (full_active p).safe

def region := {x : Gaia | x ∈ boundsEarth ∧ D.active (tap x)}
lemma region_sub : D.region ⊆ boundsEarth := fun _ h => h.1
@[simp] lemma full_region : full.region = boundsEarth := by simp [region]

@[measurability] lemma region_meas : MeasurableSet D.region :=
  earth_meas.inter <| measurableSet_Ioi.preimage
    (D.mark_continuous.comp tap_smooth.continuous).measurable

lemma region_finite : volume D.region ≠ ⊤ :=
  ne_top_of_le_ne_top earth_oaks (measure_mono D.region_sub)

private lemma ae_coordinate_ne (i : Axis) (y : ℝ) :
    ∀ᵐ x : Gaia ∂volume, x i ≠ y := by
  rw [ae_iff]; simp only [ne_eq, not_not]
  let s := (eval i : Track → ℝ) ⁻¹' {y}
  change volume (exileE ⁻¹' s) = 0
  rw [(EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp Axis).measure_preimage
    (s:=s) (by exact MeasurableSet.nullMeasurableSet <|
      (measurableSet_singleton _).preimage (continuous_apply i).measurable), volume_pi]
  exact Measure.pi_eval_preimage_null _ (measure_singleton y)

lemma ae_mark_ne (r : ℝ) :
    ∀ᵐ x : Gaia ∂volume, D.mark (tap x) ≠ r := by
  have hz := side_pos D.cycle
  let u (x : Gaia) (n : ℤ) := (D.cycle.val:ℝ) * x 3 - 2 * Real.pi * n
  have hu (y : ℝ) : ∀ᵐ x : Gaia ∂volume, ∀ n : ℤ, u x n ≠ y := by
    rw [ae_all_iff]
    intro n
    filter_upwards [ae_coordinate_ne 3 ((y + 2 * Real.pi * n) / D.cycle.val)] with x hx hc
    exact hx ((eq_div_iff hz.ne').mpr (by unfold u at hc; linarith))
  filter_upwards [hu r, hu (-r)] with x hx hx' hc

  unfold mark at hc; rw [tap_angle] at hc
  obtain ⟨n, hn⟩ := wrapDist_hits ((D.cycle.val:ℝ) * x 3)
  have hn : |u x n| = r := hn.trans hc
  by_cases h : 0 ≤ u x n
  · exact hx n ((abs_of_nonneg h).symm.trans hn)
  exact hx' n (neg_eq_iff_eq_neg.mp ((abs_of_neg (lt_of_not_ge h)).symm.trans hn))

end Latitude
end ExactRunning

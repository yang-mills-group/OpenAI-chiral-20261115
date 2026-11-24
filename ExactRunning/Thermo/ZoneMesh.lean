import ExactRunning.Thermo.Latitude

/-!
# Internal momentum sampling

Mesh convergence in real momentum coordinates; using `lift`, values in
(-π,π] are right endpoint tags when the side is even and midpoints when
odd. No periodicity hypotheses needed.
-/
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix MeasureTheory
open scoped BigOperators ContDiff Topology ENNReal ComplexConjugate Matrix


namespace ZoneMesh

def angle (m : Side) := 2 * Real.pi / (m.val:ℝ)
lemma angle_pos (m) : 0 < angle m := by
  have := side_pos m
  unfold angle; positivity

section scalar
variable {m : Side}

def shift (m : Side) : ℤ := (m.val+1)/2

def rightPt (m : Side) (j : ℤ) : ℝ :=
  -Real.pi + angle m * (j + shift m)

def part (m : Side) (j : ℤ) := Set.Ioc (rightPt m j - angle m) (rightPt m j)

lemma part_iff {j : ℤ} {x : ℝ} :
    x ∈ part m j ↔ ⌈(x + Real.pi) / angle m⌉ = j + shift m := by
  rw [part,rightPt,Set.mem_Ioc, Int.ceil_eq_iff, lt_div_iff₀ (angle_pos _),
    div_le_iff₀ (angle_pos _), Int.cast_add]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

lemma angle_mul (m) : angle m * m.val = 2 * Real.pi :=
  div_mul_cancel₀ _ (side_pos m).ne'

lemma centered_iff (x : ℝ) (m) :
    x ∈ Set.Ioc (-Real.pi) Real.pi ↔
    ⌈(x + Real.pi) / angle m⌉ ∈ Set.Ioc (0:ℤ) m.val := by
  simp only [Set.mem_Ioc, Int.lt_ceil, Int.ceil_le, lt_div_iff₀ (angle_pos m),
    div_le_iff₀ (angle_pos m), Int.cast_zero, Int.cast_natCast]
  constructor <;> intro h <;> constructor <;> nlinarith [angle_mul m,h.1,h.2]

lemma shift_iff (m) (j : ℤ) :
    j * 2 ∈ Set.Ioc (-m.val:ℤ) m.val ↔
    j+shift m ∈ Set.Ioc (0 : ℤ) m.val := by
  simp only [Set.mem_Ioc, shift]
  omega

lemma partTag (m) (j : ℤ) :
    angle m * j ∈ part m j := by
  rw [part,rightPt,Set.mem_Ioc]
  have ht : (m.val:ℝ) ≤ (shift m:ℝ)*2 :=
    by exact_mod_cast (show (m.val:ℤ) ≤ shift m*2 by unfold shift; omega)
  have hu : (shift m:ℝ)*2 < (m.val:ℝ)+2 :=
    by exact_mod_cast (show shift m*2 < (m.val:ℤ)+2 by unfold shift; omega)
  have h₁ := mul_lt_mul_of_pos_left hu (angle_pos m)
  have h₂ := mul_le_mul_of_nonneg_left ht (angle_pos m).le
  constructor <;> linarith [angle_mul m]

end scalar

section zones
variable {m : Side}

def zones (p : Site m) : Set Gaia :=
  {x | ∀ i, x i ∈ part m (lift p i)}

lemma zone_meas (p : Site m) : MeasurableSet (zones p) :=
  (MeasurableSet.univ_pi' (X:=fun _=>ℝ) (t:=fun i=>part m (lift p i))
    fun _ => measurableSet_Ioc).preimage exileE.measurable

lemma zone_sub (p : Site m) : zones p ⊆ boundsEarth := by
  intro x hx i
  change x i ∈ _
  rw [centered_iff _ m, part_iff.mp (hx i)]
  exact (shift_iff m _).mp (ZMod.valMinAbs_mem_Ioc _)

lemma zone_unique {p q : Site m} {x : Gaia} (h : x∈zones p) (he : x∈zones q) :
    p = q := by
  funext i
  exact ZMod.injective_valMinAbs (add_right_cancel
    ((part_iff.mp (h i)).symm.trans (part_iff.mp (he i))))

def roundTo (m : Side) (x : Gaia) : Site m :=
  wrap m fun i => ⌈(x i + Real.pi) / angle m⌉ - shift m

lemma zone_round (m : Side) {x} (h : x ∈ boundsEarth) : x ∈ zones (roundTo m x) := by
  intro i; rw [part_iff, ← sub_eq_iff_eq_add]
  refine Eq.symm ((ZMod.valMinAbs_spec _ _).mpr ⟨rfl,?_⟩)
  rw [shift_iff,sub_add_cancel,← centered_iff]
  exact h i

/-- Upper-coordinate distances O(side⁻¹), leading to convergence. -/
def zoneTag (p : Site m) := exileE.symm (fun i=>angle m * lift p i)
lemma tag_mem (p : Site m) : zoneTag p ∈ zones p :=
  fun i => partTag m (lift p i)

lemma tag_phase (p : Site m) : tap (zoneTag p) = mon p := by
  funext i
  change ((angle m * lift p i : ℝ):ℂ) =
    (m.val:ℂ)⁻¹ * (2 * Real.pi * (lift p i : ℤ))
  unfold angle
  push_cast
  ring

lemma zone_volume (p : Site m) : volume.real (zones p) = (angle m)^4 := by
  let s := fun i => part m (lift p i)
  have he : zones p = exileE ⁻¹' (Set.univ.pi s) := by ext; simp [zones,s]
  rw [Measure.real, he,
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp Axis).measure_preimage
      (MeasurableSet.univ_pi (t:=s) (fun _ => measurableSet_Ioc)|>.nullMeasurableSet),
    volume_pi_pi, ENNReal.toReal_prod]
  have ha := angle_pos m
  simp [s,part, Real.volume_Ioc, ha.le]

lemma zone_close (p : Site m) {x y} (hx : x∈zones p) (hy : y∈zones p) (i : Axis) :
    |x i - y i| ≤ angle m := by
  rw [abs_le]; constructor <;> linarith [(hx i).1,(hx i).2,(hy i).1,(hy i).2]
end zones

lemma tag_tendsto {m : ℕ → Side} (h : Tendsto (fun i => (m i).val) atTop atTop)
    {x} (hx : x∈boundsEarth) :
    Tendsto (fun i => zoneTag (roundTo (m i) x)) atTop (𝓝 x) := by
  have ht : Tendsto (fun i => angle (m i)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp h)
  let f : ℕ → Track := fun i j => zoneTag (roundTo (m i) x) j
  have hp : Tendsto f atTop (𝓝 (exileE x)) := by
    apply tendsto_pi_nhds.mpr; intro j
    rw [tendsto_iff_dist_tendsto_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => dist_nonneg)
      (fun i => zone_close _ (tag_mem _) (zone_round _ hx) _)
  have he : Continuous exileE.symm :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Axis => ℝ)).symm.continuous
  exact he.continuousAt.tendsto.comp hp

section steps

def stepFn (u : Gaia → ℂ) (m : Side) (x : Gaia) :=
  ∑ p : Site m, (zones p).indicator (fun _ => u (zoneTag p)) x

private lemma finiteVol : IsFiniteMeasure (volume.restrict boundsEarth) := by
  constructor
  rw [Measure.restrict_apply_univ]
  exact lt_top_iff_ne_top.mpr earth_oaks

lemma step_meas (u m) : Measurable (stepFn u m) :=
  Finset.measurable_fun_sum univ fun p _ =>
    measurable_const.indicator (zone_meas p)

lemma step_integral (u m) :
    (∫ x in boundsEarth, stepFn u m x) =
      (angle m:ℂ)^4 * ∑ p : Site m, u (zoneTag p) := by
  unfold stepFn
  rw [integral_finsetSum, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [setIntegral_indicator (zone_meas p), Set.inter_eq_right.mpr (zone_sub p),
      setIntegral_const, zone_volume]
    simp
  haveI := finiteVol
  exact fun i _ => (integrable_const _).indicator (zone_meas i)

lemma step_value (u m) {x} (hx : x∈boundsEarth) :
    stepFn u m x = u (zoneTag (roundTo m x)) := by
  unfold stepFn
  rw [Fintype.sum_eq_single (roundTo m x)]
  · exact Set.indicator_of_mem (zone_round m hx) _
  exact fun p h => Set.indicator_of_notMem
    (fun he => h <| zone_unique he (zone_round m hx)) _

lemma tendsto_step {u : Gaia→ℂ} {m : ℕ → Side}
    (h : Tendsto (fun i => (m i).val) atTop atTop)
    (hc : ∀ᵐ x : Gaia ∂volume.restrict boundsEarth, ContinuousAt u x)
    (hb : ∃ B : ℝ, ∀ x∈boundsEarth, ‖u x‖ ≤ B) :
    Tendsto (fun i => ∫ x in boundsEarth, stepFn u (m i) x) atTop
      (𝓝 (∫ x in boundsEarth, u x)) := by
  obtain ⟨B, hB⟩ := hb
  haveI := finiteVol
  refine tendsto_integral_of_dominated_convergence _
    (fun i => (step_meas u _).aestronglyMeasurable)
    (integrable_const B) (fun i => ?_) ?_
  · filter_upwards [ae_restrict_mem earth_meas] with x hx
    rw [step_value _ _ hx]
    exact hB _ (zone_sub _ (tag_mem _))
  filter_upwards [hc, ae_restrict_mem earth_meas] with x ha hx
  simp_rw [step_value _ _ hx]
  exact ha.tendsto.comp (tag_tendsto h hx)

lemma tendsto_shop {f : Momentum → ℂ} {m : ℕ → Side}
    (h : Tendsto (fun i => (m i).val) atTop atTop)
    (hc : ∀ᵐ x ∂volume.restrict boundsEarth, ContinuousAt (f ∘ tap) x)
    (hb : ∃ B : ℝ, ∀ x∈boundsEarth, ‖f (tap x)‖ ≤ B) :
    Tendsto (fun i => shop (m i) f) atTop
      (𝓝 (cartWeight * ∫ x in boundsEarth, f (tap x))) := by
  refine (tendsto_step h hc hb |>.const_mul (cartWeight:ℂ)).congr fun i => ?_
  simp_rw [shop, step_integral, Function.comp_apply, tag_phase, ← mul_assoc]
  congr 1
  have h₀ : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold cartWeight angle cents
  rw [show Fintype.card (Site (m i)) = (m i).val^4 by simp]
  push_cast
  field_simp [side_ne]
end steps
end ZoneMesh
end ExactRunning

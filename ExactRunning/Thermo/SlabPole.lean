import ExactRunning.Thermo.Unmask

/-!
# Contribution of the peeled endpoint integrand on an IR latitude

Approach: compare directly to `poleSpin` (archive). In the radial
shell, using sharp slabs instead of radial lower cutoff only loses
a collar |x₃|≤d, with r^-4 integral uniformly bounded.
-/
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix MeasureTheory
open scoped BigOperators ContDiff Topology ENNReal ComplexConjugate Matrix

namespace SlabPole
open Metric

lemma coord_le (x : Gaia) (i : Axis) : |x i| ≤ ‖x‖ :=
  show ‖(exileE x i)‖ ≤ ‖x‖ from
    (norm_le_pi_norm (exileE x) i).trans (orbit_at _)

def poleCost (G : Gauge) := |4 * G.casimir| * 6

lemma poleCost_nonneg (G) : 0 ≤ poleCost G := by
  unfold poleCost; positivity

section pole
variable {x : Gaia}
lemma pole_cap (G) (hx : 0<‖x‖) : |poleVec G (exileE x)| ≤ poleCost G / ‖x‖^4 := by
  have hs (i) : (x i)^2 ≤ ‖x‖^2 := sq_le_sq.mpr (by simpa using coord_le x i)

  rw [poleVec, abs_mul,poleCost, mul_div_assoc |4 * G.casimir|]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  refine (abs_sub ..).trans <|
    (add_le_add_left (abs_sub ..) _).trans ?_
  change |(x 1)^2 / ‖x‖^6| + |4*(x 1)^2*(x 0)^2/‖x‖^8| + |(‖x‖^4)⁻¹| ≤ _
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
  calc
    _ ≤ ‖x‖^2 / ‖x‖^6 + 4*‖x‖^2*‖x‖^2 / ‖x‖^8 + (‖x‖^4)⁻¹ := by
      gcongr ?_ / _ + _*?_ * ?_ / _ + _ <;> exact hs _
    _ = _ := by field_simp; ring
end pole

section box
variable (s a : ℝ)

def widths (i : Axis) := if i=3 then s else a
def box : Set Gaia := { x | ∀ i : Axis, x i ∈ Set.Icc (-(widths s a i)) (widths s a i) }

lemma box_closed : IsClosed (box s a) := by
  simp only [box, Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_Icc.preimage (by fun_prop)

variable {s a}

lemma box_mem {x : Gaia} (h : ‖x‖ ≤ a) (he : |x 3| ≤ s) : x ∈ box s a := by
  intro i
  rw [Set.mem_Icc, ← abs_le, widths]
  split
  next hg => exact hg.symm ▸ he
  exact (coord_le x i).trans h

lemma box_ereal (ha : 0 < a) (_hs : 0 < s) :
    volume (box s a) = ENNReal.ofReal ((2*a)^3 * (2*s)) := by

  let I := fun i => Set.Icc (-(widths s a i)) (widths s a i)
  have he : box s a = exileE ⁻¹' (Set.univ.pi I) := by ext; simp [box,I,forall_and]; rfl
  rw [he,
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp Axis).measure_preimage
      (MeasurableSet.univ_pi (t:=I) (fun _ => measurableSet_Icc)|>.nullMeasurableSet),
    volume_pi_pi, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
  simp [I,Real.volume_Icc,widths, Fin.prod_univ_four, two_mul]; ring

lemma box_finite (ha : 0 < a) (hs : 0 < s) :
    volume (box s a) ≠ ⊤ := by
  rw [box_ereal ha hs]; exact ENNReal.ofReal_ne_top

lemma box_real (ha : 0 < a) (hs : 0 < s) :
    volume.real (box s a) = (2*a)^3*(2*s) := by
  rw [Measure.real,box_ereal ha hs,ENNReal.toReal_ofReal (by positivity)]
end box

section collar
private lemma collar_budget {s C : ℝ} (hs : 0<s) (hC : 0≤C)
    {f : Gaia → ℝ} (n : ℕ)
    {S : Set Gaia} (hS : MeasurableSet S) (hf : IntegrableOn f S volume)
    (hm : ∀ x∈S, ‖f x‖ ≤ C / ‖x‖^4)
    {a : ℝ} (ha : 0<a)
    (hv : ∀ x∈S, |x 3| ≤ s ∧ a < ‖x‖ ∧ ‖x‖ ≤ 2^n * a) :
    ‖∫ x in S, f x‖ ≤ 256*C*s/a := by
  induction n generalizing S a with
  | zero =>
    have h : S = ∅ := Set.eq_empty_iff_forall_notMem.mpr <| by
      intro x hx
      exact (lt_self_iff_false a).mp
        ((hv x hx).2.1.trans_le (by simpa using (hv x hx).2.2))
    rw [h]; simp only [setIntegral_empty, norm_zero]
    positivity
  | succ n ih =>
    let T := S ∩ closedBall (0:Gaia) (2*a)
    have hst : T ⊆ S := Set.inter_subset_left
    have hT : MeasurableSet T := hS.inter measurableSet_closedBall
    have hba : 0 < 2*a := by positivity

    have h1 : ‖∫ x in T, f x‖ ≤ 128*C*s/a := by
      have ht : T ⊆ box s (2*a) := fun x hx =>
        box_mem (by simpa using hx.2) (hv x hx.1).1
      have hu : ∀ x∈T, ‖f x‖ ≤ C/a^4 := fun x hx =>
        (hm x hx.1).trans (div_le_div_of_nonneg_left hC (pow_pos ha _) <|
          pow_le_pow_left₀ ha.le (hv x hx.1).2.1.le _)
      refine (norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.mpr <|
        ne_top_of_le_ne_top (box_finite hba hs) (measure_mono ht)) hu).trans ?_
      exact (mul_le_mul_of_nonneg_left
        (measureReal_mono ht (box_finite hba hs)) (by positivity)).trans_eq
        (by rw [box_real hba hs]; field_simp; ring)
    have h2 : ‖∫ x in S \ T, f x‖ ≤ 256*C*s/(2*a) := by
      refine ih (hS.diff hT) (hf.mono_set Set.sdiff_subset) (fun x hx => hm _ hx.1)
        hba ?_
      intro x hx
      exact ⟨(hv _ hx.1).1, lt_of_not_ge
        (fun hh => hx.2 ⟨hx.1, by simpa using hh⟩),
        (hv _ hx.1).2.2.trans_eq (by ring)⟩

    rw [setIntegral_sdiff hT hf hst] at h2
    let H := ∫ x in S, f x
    let H1 := ∫ x in T, f x
    change ‖H‖ ≤ _
    rw [← sub_add_cancel H H1]
    exact (norm_add_le ..).trans ((add_le_add h2 h1).trans_eq (by ring))

lemma collar_bound (G : Gauge) {d} (hd : 0<d) :
    ‖∫ x in (orbShell d) \ (Latitude.native d).region, poleVec G (exileE x)‖ ≤
      256 * poleCost G := by
  obtain ⟨n,hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt
    (by norm_num : (1:ℝ)<2)).eventually (eventually_ge_atTop (1/d))).exists
  have hn' : 1 ≤ 2^n*d := (div_le_iff₀ hd).mp hn
  have hp := poleBudget (G:=G) hd
  have hc := collar_budget hd (poleCost_nonneg G) n
      (shell_meas.diff (Latitude.region_meas (Latitude.native d)))
      (hp.mono_set Set.sdiff_subset) ?m hd ?u
  case m =>
    exact fun x hx => pole_cap _ (hd.trans hx.1.1)
  case u =>
    intro x hx
    refine ⟨le_of_not_gt (fun h=> hx.2 ⟨shell_on hx.1,?_⟩), hx.1.1,
      hx.1.2.trans hn'⟩
    rw [Latitude.active,Latitude.native_cradle (shell_on hx.1)]
    exact h
  exact hc.trans_eq (by field_simp)
end collar

section norm
variable {d A C : ℝ} {f : Momentum → ℂ}

def charge (G : Gauge) (A C : ℝ) :=
  cartWeight * (A * volume.real boundsEarth + C * (2*Real.pi^2) + 256 * poleCost G)

lemma charge_nonneg (G) (ha : 0 ≤ A) (hc : 0 ≤ C) : 0 ≤ charge G A C := by
  have := cart_weight_pos; have := poleCost_nonneg G
  unfold charge cartWeight; positivity

lemma absoluteLatitude (G)
    (hd : 0<d) (hu : d≤1) (hA : 0≤A) (hC : 0≤C)
    (hf : IntegrableOn (f ∘ tap) (Latitude.native d).region volume)
    (houter : ∀ x∈(Latitude.native d).region, ‖f (tap x)‖ ≤ A/‖x‖^4)
    (hinner : ∀ x∈(Latitude.native d).region,
      ‖f (tap x) - ↑(poleVec G (exileE x))‖ ≤ C/‖x‖^3) :
    |((Latitude.native d).mean f).re + G.slopeConstant * Real.log d⁻¹| ≤ charge G A C := by
  let U := (Latitude.native d).region
  let V := orbShell d
  let u x := (f (tap x)).re
  let v x := poleVec G (exileE x)
  have hU := Latitude.region_meas (Latitude.native d)
  have hV : MeasurableSet V := shell_meas
  have hu1 := hf.re
  have hv1 := poleBudget (G:=G) hd
  let S := U ∩ V

  have hS : MeasurableSet S := hU.inter hV
  have hu1 : IntegrableOn u U volume := hu1
  have hv1 : IntegrableOn v V volume := hv1
  have inside : ‖∫ x in S, u x - v x‖ ≤ C * (2*Real.pi^2) := by
    let g := fun x:Gaia=> C * (‖x‖^3)⁻¹
    have hz : IntegrableOn (fun x:Gaia=> (‖x‖^3)⁻¹) V volume := by
      simpa using geoS hd (fun _ => 1) continuous_const 3
    have hg : IntegrableOn g V volume := hz.const_mul _
    refine (norm_integral_le_of_norm_le
      (g:=g) (hg.mono_set Set.inter_subset_right : IntegrableOn g S volume) ?_).trans ?_
    · filter_upwards [ae_restrict_mem hS] with x hx
      unfold u v g
      rw [Real.norm_eq_abs, show (poleVec G (exileE x)) =
          (poleVec G (exileE x):ℂ).re from rfl, ← Complex.sub_re]
      exact (Complex.abs_re_le_norm _).trans
        ((hinner _ hx.1).trans_eq (div_eq_mul_inv ..))
    have he : ∀ x, 0 ≤ g x := by intro; unfold g; positivity
    refine (setIntegral_mono_set (s:=S) hg (Eventually.of_forall he)
      (Eventually.of_forall fun _ hx=> (show _ from hx.2))).trans ?_

    unfold g V
    rw [integral_const_mul, (peel_p _ hd hu).1]
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right (by positivity) (by linarith)) hC
  have outside : ‖∫ x in U \ S,u x‖ ≤ A * volume.real boundsEarth := by
    have he : U \ S ⊆ boundsEarth := fun _ h=> h.1.1
    refine (norm_setIntegral_le_of_norm_le_const
      ((measure_mono he).trans_lt (lt_top_iff_ne_top.mpr earth_oaks))
      (C:=A) ?_).trans ?_
    · intro x hx
      have hx' := hx.1.2
      rw [Latitude.active,Latitude.native_cradle hx.1.1] at hx'
      have hs : 1 ≤ ‖x‖ := le_of_not_gt fun h=> hx.2
        ⟨hx.1, hx'.trans_le (coord_le _ _), h.le⟩
      unfold u; rw [Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans
        ((houter _ hx.1).trans (div_le_self hA (one_le_pow₀ hs)))
    exact mul_le_mul_of_nonneg_left (measureReal_mono he earth_oaks) hA
  have collar : ‖∫ x in V \ S,v x‖ ≤ 256*poleCost G := by
    rw [show V \ S = V \ U by ext; simp [S]]
    exact collar_bound G hd

  rw [Latitude.mean, Complex.mul_re, show (∫ x in (Latitude.native d).region, f (tap x)).re =
      (∫ x in U,u x) from (integral_re hf).symm, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  have hz : - (G.slopeConstant * Real.log d⁻¹) = cartWeight*(∫ x in V,v x) :=
      (by rw [← neg_mul]; exact (poleSpin (G:=G) hd hu).symm)
  rw [← sub_neg_eq_add, hz, ← mul_sub, abs_mul, abs_of_pos cart_weight_pos]
  apply mul_le_mul_of_nonneg_left _ cart_weight_pos.le
  change |(∫ x in U,u x) - ∫ x in V,v x| ≤ _
  rw [show (∫ x in U, u x) - (∫ x in V,v x) = ((∫ x in U \ S,u x)+(∫ x in S,u x-v x)) -
      ∫ x in V \ S,v x from ?_]
  · exact (norm_sub_le ..).trans <| add_le_add ((norm_add_le ..).trans
      (add_le_add outside inside)) collar
  rw [setIntegral_sdiff hS hu1 Set.inter_subset_left,
    setIntegral_sdiff hS hv1 Set.inter_subset_right,
    integral_sub (hu1.mono_set Set.inter_subset_left : IntegrableOn u S volume)
      (hv1.mono_set Set.inter_subset_right)]
  ring
end norm

end SlabPole
end ExactRunning

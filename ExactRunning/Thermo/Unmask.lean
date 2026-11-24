import ExactRunning.Thermo.SlabMean

/-!
# Vanishing thickness limits

Incoming filters used on a transformation of ratio L excite all aliases
of the allowed coarse modes, thereby respecting the coarse-cell shift.
Compared to the native cutoff d, this can remove extra slabs also away
from zero momentum, at multiples of 2π/L in the fine zone. We
can forget those extra slabs when taking d → 0 at each
fixed transformation, thanks to gapped integrands there. No uniformity
in endpoint or even L needed for this part.
-/
noncomputable section
namespace ExactRunning.Latitude
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix MeasureTheory
open scoped BigOperators ContDiff Topology ENNReal ComplexConjugate Matrix


/-- IR cutoff `d` in the native lattice units. -/
def native (d : ℝ) : Latitude := ⟨1,d⟩

/-- Pull back the IR cutoff from coarse lattice, coarse radius Ld. -/
def incoming (L : Side) (d : ℝ) : Latitude := ⟨L,L.val*d⟩

lemma incoming_one (d) : incoming 1 d = native d := by simp [native,incoming]

section sets
variable {L : Side} {d : ℝ} {p : Momentum}

lemma native_of_incoming (hp : (incoming L d).active p) : (native d).active p := by
  apply lt_of_mul_lt_mul_left _ (side_pos L).le
  exact (show _ < wrapDist (L.val * (p 3).re) from hp).trans_le
    ((wrapDist_nat_mul_le ..).trans_eq (by simp [native, mark]))

lemma incoming_sub (L) (d) : (incoming L d).region ⊆ (native d).region :=
  fun _ h => ⟨h.1, native_of_incoming h.2⟩

lemma native_cradle {x} (h : x∈boundsEarth) (d) :
    (native d).mark (tap x) = |x 3| := by
  simp only [mark,native,tap_angle, PNat.one_coe, Nat.cast_one, one_mul]
  exact wrapDist_eq (cradleFront _ h 3)

lemma diff_subset (L) (d) :
    (native d).region \ (incoming L d).region ⊆
      (native (Real.pi / L.val)).region := by
  rintro x ⟨hx,hy⟩
  refine ⟨hx.1, ?_⟩
  rw [active, native_cradle hx.1]
  apply lt_of_not_ge
  intro hn
  apply hy
  refine ⟨hx.1,?_⟩
  have hl : |L.val * (x 3)| ≤ Real.pi := by
    rw [abs_mul, Nat.abs_cast, mul_comm]
    exact (le_div_iff₀ (side_pos L)).mp hn

  change (L.val:ℝ) * d < wrapDist (L.val * (x 3))
  rw [wrapDist_eq hl, abs_mul, Nat.abs_cast, ← native_cradle hx.1 d]
  exact mul_lt_mul_of_pos_left hx.2 (side_pos L)
end sets

variable {g : Gaia → ℂ}

private lemma tendsto_zone (L : Side) (hf : IntegrableOn g boundsEarth volume) :
    Tendsto (fun d => ∫ x in (incoming L d).region, g x)
      (𝓝[>] 0) (𝓝 (∫ x in boundsEarth, g x)) := by
  let S d := (incoming L d).region
  have he d : (∫ x in boundsEarth, (S d).indicator g x) = ∫ x in (incoming L d).region, g x := by
    rw [setIntegral_indicator (region_meas _), Set.inter_eq_right.mpr (region_sub _)]
  simp_rw [← he]
  apply tendsto_integral_filter_of_dominated_convergence
    (bound:=fun x=> ‖g x‖)
  · exact Eventually.of_forall fun d =>
      hf.aestronglyMeasurable.indicator (region_meas _)
  · exact Eventually.of_forall fun d =>
      Eventually.of_forall fun x=> by by_cases h:x∈S d <;> simp [h]
  · exact hf.norm

  let E := incoming L 0
  filter_upwards [ae_restrict_mem earth_meas, ae_restrict_of_ae (E.ae_mark_ne 0)] with x hx hz
  have hp := (E.mark_nonneg (tap x)).lt_of_ne' hz
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(eventually_lt_nhds (div_pos hp (side_pos L))).filter_mono
    nhdsWithin_le_nhds] with d hd
  have h : x∈S d := ⟨hx,(lt_div_iff₀' (side_pos L)).mp hd⟩
  exact (Set.indicator_of_mem h g).symm

lemma tendsto_incoming (L) {f} (hf : IntegrableOn (f ∘ tap) boundsEarth volume) :
    Tendsto (fun d => (incoming L d).mean f) (𝓝[>] 0) (𝓝 (full.mean f)) := by
  rw [mean, full_region]; exact (tendsto_zone L hf).const_mul _
lemma tendsto_native {f} (hf : IntegrableOn (f ∘ tap) boundsEarth volume) :
    Tendsto (fun d => (native d).mean f) (𝓝[>] 0) (𝓝 (full.mean f)) := by
  simpa only [incoming_one] using tendsto_incoming 1 hf

lemma tendsto_native_sub (L : Side) {f}
    (hf : ∀ d:ℝ, 0<d → IntegrableOn (f ∘ tap) (native d).region volume) :
    Tendsto (fun d => (native d).mean f - (incoming L d).mean f)
      (𝓝[>] 0) (𝓝 (0:ℂ)) := by
  let D := native (Real.pi / L.val)
  let u := f ∘ tap
  let g := D.region.indicator u
  have hg : Integrable g volume := by
    rw [show g = _ from rfl, integrable_indicator_iff D.region_meas]
    exact hf _ (div_pos Real.pi_pos (side_pos L))
  have hz : Tendsto (fun d => (cartWeight:ℂ) *
      ((∫ x in (native d).region, g x) - ∫ x in (incoming L d).region, g x))
      (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
    simpa only [sub_self, mul_zero,incoming_one] using ((tendsto_zone 1 hg.integrableOn
      ).sub (tendsto_zone L hg.integrableOn)).const_mul (cartWeight:ℂ)
  refine hz.congr' ?_

  filter_upwards [self_mem_nhdsWithin] with d hd
  simp_rw [mean, ← mul_sub]
  refine congrArg _ ?_
  rw [← setIntegral_sdiff (region_meas _) hg.integrableOn (incoming_sub L d)]
  refine Eq.trans ?_ (setIntegral_sdiff (region_meas _) (hf d hd) (incoming_sub L d))
  exact setIntegral_congr_fun ((region_meas _).diff (region_meas _))
    fun x hx=> Set.indicator_of_mem (diff_subset L d hx) u

lemma tendsto_radius {r : ℝ} (hr : 0<r) :
    Tendsto (fun d:ℝ => r*d) (𝓝[>] 0) (𝓝[>] 0) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (by simpa only [id_eq,mul_zero] using
      (Tendsto.const_mul r (tendsto_id.mono_left
        (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)))
    )
    (Eventually.mono self_mem_nhdsWithin fun _ hd => mul_pos hr hd)

end ExactRunning.Latitude

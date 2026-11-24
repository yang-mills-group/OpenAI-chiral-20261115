import ExactRunning.Thermo.ZoneMesh
import ExactRunning.Calc.Touch

/-!
# Thermodynamic integration on an internal latitude

Compactness near safe region suffices for each fixed cutoff. Complex
analyticity of lattice integrands (where applicable) can enter *only*
via real regularity; no holomorphic version of a sharp mask assumed.
-/

noncomputable section
namespace ExactRunning.Latitude
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix MeasureTheory
open scoped BigOperators ContDiff Topology ENNReal ComplexConjugate Matrix


variable (D : Latitude)

def mean (f : Momentum → ℂ) :=
  (cartWeight : ℂ) * ∫ x in D.region, f (tap x)

def mask (f : Momentum → ℂ) (q : Momentum) :=
  if D.active q then f q else 0

def mesh (m : Side) (f : Momentum → ℂ) :=
  shop m (D.mask f)

/-- The closed region used for bounds may be bigger than the closure. -/
def closedRegion := {x ∈ Metric.closedBall (0:Gaia) (2 * Real.pi) | D.safe (tap x)}
lemma closedRegion_compact : IsCompact D.closedRegion :=
  (isCompact_closedBall ..).inter_right
    (isClosed_le continuous_const (D.mark_continuous.comp tap_smooth.continuous))
lemma region_subset_closed : D.region ⊆ D.closedRegion :=
  fun _ h => ⟨earth_bounded _ h.1,h.2.safe⟩

section scalar
variable {f : Momentum → ℂ}

lemma integrableOn {g : Gaia → ℂ}
    (hf : ∀ x, D.safe (tap x) → ContinuousAt g x) :
    IntegrableOn g D.region volume :=
  (ContinuousOn.integrableOn_compact D.closedRegion_compact
    (show ContinuousOn g _ from fun x hx=> (hf x hx.2).continuousWithinAt)).mono_set
      D.region_subset_closed

lemma mask_mean :
    mean full (D.mask f) = D.mean f := by
  let s := {x : Gaia | D.active (tap x)}
  have hm : MeasurableSet s :=
    measurableSet_Ioi.preimage (D.mark_continuous.comp tap_smooth.continuous).measurable
  have hs : ∀ x, D.mask f (tap x) = s.indicator (f ∘ tap) x := fun x => by
    by_cases h : D.active (tap x)
    · rw [Set.indicator_of_mem (show x∈s from h), mask, if_pos h]; rfl
    rw [Set.indicator_of_notMem (show x∉s from h), mask, if_neg h]
  rw [mean,full_region, funext hs, setIntegral_indicator hm]; rfl

lemma tendsto_mesh {m : ℕ → Side}
    (ht : Tendsto (fun n => (m n).val) atTop atTop)
    (hf : ∀ x : Gaia, D.safe (tap x) → ContinuousAt (f ∘ tap) x) :
    Tendsto (fun n => D.mesh (m n) f) atTop (𝓝 (D.mean f)) := by
  rw [← mask_mean, mean, full_region]
  refine ZoneMesh.tendsto_shop ht ?_ ?_

  · refine ae_restrict_of_ae ?_
    filter_upwards [D.ae_mark_ne D.radius] with x hx
    have he := (D.mark_continuous.comp tap_smooth.continuous).continuousAt (x:=x)
    rcases hx.lt_or_gt with h|h
    · refine (continuousAt_const (y:=(0:ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [he.eventually_lt_const h] with y hy
      exact if_neg hy.not_gt
    refine (hf x h.le).congr_of_eventuallyEq ?_
    filter_upwards [he.eventually_const_lt h] with y hy
    exact if_pos hy
  have he : ContinuousOn (f ∘ tap) D.closedRegion :=
    fun x hx=> (hf x hx.2).continuousWithinAt
  obtain ⟨B,hB⟩ := (D.closedRegion_compact.image_of_continuousOn he.norm).bddAbove
  refine ⟨max B 0, ?_⟩
  intro x hx
  unfold mask
  split
  · rename_i hz
    exact le_max_of_le_left (hB ⟨x, D.region_subset_closed ⟨hx,hz⟩, rfl⟩)
  simp

lemma mean_congr {g : Momentum→ℂ}
    (h : ∀ x∈D.region, f (tap x) = g (tap x)) :
    D.mean f = D.mean g := by
  unfold mean; rw [setIntegral_congr_fun D.region_meas h]

lemma mean_add {g : Momentum → ℂ} (h : IntegrableOn (f ∘ tap) D.region volume)
    (he : IntegrableOn (g ∘ tap) D.region volume) :
    D.mean (f+g) = D.mean f + D.mean g := by
  change cartWeight * (∫ x in D.region,(f ∘ tap) x + (g ∘ tap) x) = _
  rw [MeasureTheory.integral_add h he,mul_add]
  rfl

lemma mean_sub {g : Momentum → ℂ} (h : IntegrableOn (f ∘ tap) D.region volume)
    (he : IntegrableOn (g ∘ tap) D.region volume) :
    D.mean (f-g) = D.mean f - D.mean g := by
  change cartWeight * (∫ x in D.region,(f ∘ tap) x - (g ∘ tap) x) = _
  rw [integral_sub h he,mul_sub]
  rfl

lemma mean_const_mul (c : ℂ) : D.mean (fun p => c*f p) = c * D.mean f := by
  rw [mean,integral_const_mul,mean,mul_left_comm]

end scalar

section curve

/-- The frequency tests, on a real parameter (tilt) and internal momentum. -/
def Regular (F : ℝ → Momentum → ℂ) :=
  ∀ z, D.safe (tap z.2) →
    ContDiffAt ℝ ω (fun w : ℝ × Gaia => F w.1 (tap w.2)) z

def diff (F : ℝ → Momentum → ℂ) := fun (t : ℝ) (p : Momentum) => deriv (fun s=> F s p) t

variable {D} {F : ℝ → Momentum → ℂ}

namespace Regular
lemma fixed (h : D.Regular F) (t : ℝ) :
    ∀ x, D.safe (tap x) → ContinuousAt (F t ∘ tap) x :=
  fun x hx => (h (t,x) hx).continuousAt.comp (continuousAt_const.prodMk continuousAt_id)

lemma integrable (h : D.Regular F) (t : ℝ) :
    IntegrableOn (F t ∘ tap) D.region volume :=
  D.integrableOn (h.fixed t)

lemma diffReg (h : D.Regular F) : D.Regular (diff F) := by
  intro z hz
  let g := fun w : ℝ × Gaia => F w.1 (tap w.2)
  change ContDiffAt ℝ ω (plunge g) z
  have he : ContDiffAt ℝ ω g z := h z hz
  refine ((he.fderiv_right (m:=ω) (by simp)).clm_apply
    (contDiffAt_const (c:=((1,0) : ℝ × Gaia)))).congr_of_eventuallyEq ?_
  filter_upwards [he.eventually (by simp)] with w hw

  apply HasDerivAt.deriv
  have hx : HasFDerivAt g (fderiv ℝ g w) ((fun t => (t, w.2)) w.1) :=
    (hw.differentiableAt (by simp)).hasFDerivAt
  exact hx.comp_hasDerivAt (f:=fun t => (t,w.2)) w.1
    ((hasDerivAt_id w.1).prodMk (hasDerivAt_const ..))

lemma derivAt (h : D.Regular F) (t : ℝ) :
    HasDerivAt (fun s => D.mean (F s)) (D.mean (diff F t)) t := by
  let S := Metric.closedBall t 1 ×ˢ D.closedRegion
  have hs : IsCompact S := (isCompact_closedBall ..).prod D.closedRegion_compact
  have hp : ContinuousOn (fun w => ‖diff F w.1 (tap w.2)‖) S :=
    fun x hx => (h.diffReg x hx.2.2).continuousAt.norm.continuousWithinAt
  obtain ⟨B,hB⟩ := (hs.image_of_continuousOn hp).bddAbove
  haveI : IsFiniteMeasure (volume.restrict D.region) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr D.region_finite⟩
  apply HasDerivAt.const_mul
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds t zero_lt_one)
    (F:=fun s x=> F s (tap x)) (F':=fun s x=> diff F s (tap x))
    (Eventually.of_forall fun s => (h.integrable s).aestronglyMeasurable)
    (h.integrable t)
    (h.diffReg.integrable t).aestronglyMeasurable ?_
    (integrable_const B) ?_).2
  · filter_upwards [ae_restrict_mem D.region_meas] with x hx y hy
    exact hB ⟨(y,x),⟨Metric.ball_subset_closedBall hy, D.region_subset_closed hx⟩, rfl⟩

  filter_upwards [ae_restrict_mem D.region_meas] with x hx y _
  have he : ContDiffAt ℝ ω (fun z => F z (tap x)) y :=
    (h (y,x) hx.2.safe).comp y (contDiffAt_id.prodMk contDiffAt_const)
  exact (he.differentiableAt (by simp)).hasDerivAt

lemma deriv_mean (h : D.Regular F) :
    deriv (fun t => D.mean (F t)) = (fun t=> D.mean (diff F t)) :=
  funext fun t => (h.derivAt t).deriv

lemma smooth (h : D.Regular F) : ContDiff ℝ ∞ (fun t => D.mean (F t)) := by
  rw [contDiff_infty]; intro n
  induction n generalizing F with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.mpr fun t=> (h.derivAt t).continuousAt
  | succ n ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_deriv, h.deriv_mean]
    refine ⟨fun t=> (h.derivAt t).differentiableAt, ?_,ih h.diffReg⟩
    simp

/-- Peeling a quadratic coefficient. -/
lemma quad_mean (h : D.Regular F) :
    quad (fun t => D.mean (F t)) =
    D.mean (fun p => quad (fun t=> F t p)) := by
  have he (f : ℝ→ℂ) : quad f = (2:ℂ)⁻¹ * deriv (deriv f) 0 := by
    rw [quad, Complex.real_smul, Complex.ofReal_inv, ← plunge_dive, Complex.ofReal_ofNat]
    rfl
  simp_rw [he,h.deriv_mean,h.diffReg.deriv_mean,mean_const_mul]
  rfl

lemma quad_regular (h : D.Regular F) (x) (hx : D.safe (tap x)) :
    ContDiffAt ℝ ω (fun y=> quad (fun t=> F t (tap y))) x := by
  change ContDiffAt ℝ ω (fun y => (2⁻¹:ℝ) • flareY 2 (fun t=> F t (tap y))) _
  simp_rw [plunge_dive]
  exact ((h.diffReg.diffReg (0,x) hx).comp x (contDiffAt_const.prodMk contDiffAt_id)).const_smul _
end Regular
end curve

end ExactRunning.Latitude

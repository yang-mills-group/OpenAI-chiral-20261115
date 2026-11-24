import YM.SU5.MacroSix.TestDensity
import YM.SU5.MacroSix.AnalyticWindow
import YM.SU5.MacroSix.Projections

/-!
# Product form in the question & its spectral costs

Any compactly supported smooth density product (three-dimensional transverse, one
dimensional time). No condition of smallness of transverse support. Use full π coordinates
in physical, ℂ integral of `measureField` is real-smear costs, no spectral projection for
the weights themselves.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MacroSix.ClockTest
open Function Filter Metric Finset MeasureTheory Mink Complex
open OS OS.Semigroup.Balloon Cheer Boundary Probe
open scoped Topology BigOperators NNReal ENNReal ComplexOrder ContDiff

abbrev Space := SpaceAxis → ℝ
abbrev Full := Axis → ℝ

def trans (x : Full) : Space := fun i ↦ x i.castSucc
def clock (x : Full) : ℝ := x timeAxis
def timespace : Full ≃ᵐ ℝ × Space := MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) timeAxis
def bankOf (x : Full) : OS.Cross timeAxis := shore (WithLp.toLp 2 (trans x))

lemma clock_smooth : ContDiff ℝ ∞ clock := contDiff_apply ℝ _ _
lemma trans_smooth : ContDiff ℝ ∞ trans := contDiff_pi.mpr fun i ↦ contDiff_apply ℝ _ _

lemma clock_entire : Continuous clock := clock_smooth.continuous
lemma trans_entire : Continuous trans := trans_smooth.continuous
lemma bank_entire : Continuous bankOf := by
  apply Continuous.subtype_mk; change Continuous (fun x : Full ↦ position _ _)
  have hc : Continuous (fun x : Full ↦ WithLp.toLp 2 (trans x)) :=
    (PiLp.continuous_toLp _ _).comp trans_entire -- name
  exact Mink.divide.symm.continuous.comp (hc.prodMk continuous_const)
lemma paid_split : MeasurePreserving timespace := volume_preserving_piFinSuccAbove (fun _ ↦ ℝ) timeAxis
lemma actual_split (x : Full) : timespace x = (clock x, trans x) := by
  apply Prod.ext; · rfl
  funext i
  change x (timeAxis.succAbove i) = x i.castSucc
  rw [Fin.succAbove_last]

noncomputable def timespaceHome : Full ≃L[ℝ] ℝ × Space :=
  LinearEquiv.toContinuousLinearEquiv {
    timespace.toEquiv with
    map_add' x y := by
      change timespace (x+y) = timespace x + timespace y; rw [actual_split,actual_split,actual_split]; rfl
    map_smul' a y := by
      change timespace (a • y) = a • timespace y; rw [actual_split,actual_split]; rfl }

-- coordinates relation to plane spectral kernel
lemma space_bill (x : Full) (p : E4) :
    plane p (bankOf x).val = wavePhase (WithLp.ofLp (spatial p)) (trans x) := by
  unfold plane wavePhase; rw [Mink.pairing]
  have he : time (bankOf x).val=0 := (bankOf x).property
  have hp : spatial (bankOf x).val = WithLp.toLp 2 (trans x) := spatial_position ..
  rw [hp,he,mul_zero,add_zero, PiLp.inner_apply]
  simp [RCLike.inner_apply,mul_comm]

structure TimeDensity (g : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ g
  compact : HasCompactSupport g
  nonneg : ∀ x, 0 ≤ g x
  mass : ∫ x, g x=1
variable (f : Space → ℝ) (g : ℝ → ℝ)
def joined (x : Full) : ℝ := g (clock x) * f (trans x)

lemma joined_support (x : Full) (h : x ∈ tsupport (joined f g)) :
     clock x ∈ tsupport g ∧ trans x ∈ tsupport f := by
  suffices he : tsupport (joined f g) ⊆ timespace ⁻¹' ((tsupport g) ×ˢ (tsupport f)) by
    specialize he h; rwa [Set.mem_preimage,actual_split] at he
  apply closure_minimal
  · intro i p; rw [Set.mem_preimage,actual_split]; exact
      ⟨subset_tsupport _ fun h ↦ p (by unfold joined; rw [h,zero_mul]),
        subset_tsupport _ fun h ↦ p (by unfold joined; rw [h,mul_zero])⟩
  exact (isClosed_tsupport g|>.prod (isClosed_tsupport f)).preimage timespaceHome.continuous

lemma joined_compact (p : HasCompactSupport f) (q : HasCompactSupport g) :
    HasCompactSupport (joined f g) :=
  (timespaceHome.toHomeomorph.isCompact_preimage.mpr (IsCompact.prod q p)).of_isClosed_subset
    (isClosed_tsupport _) fun x v ↦ by
      change timespace x ∈ (tsupport g) ×ˢ (tsupport f); rw [actual_split]; exact joined_support _ _ x v

lemma joined_integral (A : Type*) [RCLike A] (T : ℝ → A) (S : Space → A) :
    ∫ x : Full, T (clock x) * S (trans x) = (∫ x, T x)*(∫ x, S x) := by
  let U := fun x : ℝ × Space ↦ T x.1 * S x.2
  have he := MeasurePreserving.integral_comp' paid_split U
  simp_rw [actual_split] at he
  exact he.trans (integral_prod_mul ..)

lemma joined_density (p : SmoothDensity f) (q : TimeDensity g) : SmoothDensity (joined f g) := by
  refine ⟨(q.smooth.comp clock_smooth).mul (p.smooth.comp trans_smooth), joined_compact f g p.compact q.compact,
    (fun x ↦ mul_nonneg (q.nonneg _) (p.nonneg _)), ?_⟩
  unfold joined; rw [joined_integral ℝ,q.mass,p.mass,mul_one]

lemma frequency_pay (p : SmoothDensity f) : ∀ᵐ x : Space3, frequencyCost f (WithLp.ofLp x) ≠ 0 :=
  (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
    (frequencyCost_pay p.smooth.continuous p.compact p.mass)

def temporal (g : ℝ → ℝ) (w : E4) := ∫ x, g x * tinct timeAxis x.toNNReal w

lemma temporal_pos (q : TimeDensity g) (w : E4) : 0 < temporal g w := by
  let T (x : ℝ) := tinct timeAxis x.toNNReal w
  let f (x : ℝ) := g x*T x
  have hp : Continuous T := by unfold T tinct; fun_prop
  have hc : Continuous f := q.smooth.continuous.mul hp
  have hg : HasCompactSupport f := q.compact.mul_right
  have hz : ∀ x, 0 < T x := fun x ↦ Real.exp_pos _
  have hv : ∃ x, g x ≠ 0 := by
    by_contra! h; have hu : (∫ x, g x) = 0 := by simp [h]
    have ht := q.mass; rw [hu] at ht; exact zero_ne_one ht
  obtain ⟨x,h⟩ := hv
  exact hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hg (fun y ↦ mul_nonneg (q.nonneg y)
    (hz y).le) (mul_ne_zero h (hz x).ne') -- signature
end YM.MacroSix.ClockTest
#print axioms YM.MacroSix.ClockTest.joined_density
#print axioms YM.MacroSix.ClockTest.frequency_pay

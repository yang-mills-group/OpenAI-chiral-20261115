import YM.SU5.MacroSix.SpacetimeTest
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! # Why the scaled interior spectral ball grant gives a Gram test even after
macroscopic smearing. Separate L¹ kernel bills (calibrated projection). No rate in i:
indeed the signal from this ball can be attenuated by the macroscopic heat! -/
set_option autoImplicit false
noncomputable section
namespace YM.MacroSix
open Filter Function Finset Metric MeasureTheory Complex
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators
open ClockTest Projections Mink OS OS.Semigroup.Balloon Boundary Probe

variable {H : Hilbert} (S : OS.Semigroup H timeAxis)
local notation "P" => S.ℚmeasure
local notation "ν" x:max => (S.ℚmeasure.diagonal x)
local notation "R" => S.ℚmeasure.region
local notation "L" v:max => (WithLp.ofLp (spatial v))

def wage (t : ℝ≥0) (v : E4) : ℂ := 1-(↑(tinct timeAxis t v):ℂ)
def fare (t : ℝ≥0) (y : Full) (v : E4) : ℂ := heatSpace (bankOf y) (clock y).toNNReal v * wage t v

def travelVector (a : ℝ≥0) (f : Full → ℝ) (x : H) (y : Full) : H :=
  (f y:ℂ) • S.U (bankOf y) (S.E (clock y).toNNReal (x - S.E a x))
def reachVector (a : ℝ≥0) (f : Full → ℝ) (x : H) : H :=
  total H volume (travelVector S a f x)

lemma travel_cont (a : ℝ≥0) (f : Full → ℝ) (x : H) (p : Continuous f) :
    Continuous (travelVector S a f x) := by
  apply Continuous.smul (continuous_ofReal.comp p)
  apply S.cont_cross _ _ _ bank_entire
  exact (S.continuousE _).comp (continuous_real_toNNReal.comp clock_entire)
lemma travel_integrable (a : ℝ≥0) (f : Full → ℝ) (x : H) (p : SmoothDensity f) :
    Integrable (travelVector S a f x) := (travel_cont S a f x p.smooth.continuous
      |>.integrable_of_hasCompactSupport (compact_weight f p.compact _))

lemma travel_sum {J : Type*} (A : Finset J) (a : ℝ≥0) (f : Full → ℝ) (x : J → H) (c : J → ℂ)
    (y : Full) :
    travelVector S a f (∑ i ∈ A, c i • x i) y = ∑ i ∈ A, c i • travelVector S a f (x i) y := by
  simp only [travelVector, map_sum, map_smul, ← smul_sub, ← Finset.sum_sub_distrib, smul_sum]
  -- match direction
  apply Finset.sum_congr rfl; intro i u; apply smul_comm

lemma reach_sum {J : Type*} (A : Finset J) (a : ℝ≥0) (f : Full → ℝ) (x : J → H) (c : J → ℂ)
    (p : SmoothDensity f) :
    reachVector S a f (∑ i ∈ A, c i • x i)= ∑ i ∈ A, c i • reachVector S a f (x i) := by
  letI := NormedSpace.restrictScalars ℝ ℂ H.space
  letI : IsScalarTower ℝ ℂ H.space := RestrictScalars.isScalarTower ℝ ℂ H.space
  let v := travelVector S a f
  change ∫ y, travelVector S a f (∑ i ∈ A, c i • x i) y = ∑ i ∈ A, c i • ∫ y, v (x i) y
  simp_rw [travel_sum]
  rw [integral_finsetSum]; congr 1; ext i;
  · change _ = _; exact integral_smul ..
  exact fun i _ ↦ (travel_integrable S _ _ _ p).smul (c i) -- name

lemma reach_dark (a : ℝ≥0) (f : Full → ℝ) (x : H) (p : SmoothDensity f) :
    R {v : E4 | time v = 0} (reachVector S a f x)=0 := by
  letI := NormedSpace.restrictScalars ℝ ℂ H.space
  letI : IsScalarTower ℝ ℂ H.space := RestrictScalars.isScalarTower ℝ ℂ H.space
  let A := {v : E4 | time v=0}
  let T := travelVector S a f x
  have he (y) : R A (T y)=0 := by
    have h : MeasurableSet A := (isClosed_eq Mink.clock_cont continuous_const).measurableSet
    unfold T travelVector; rw [map_smul,slideHeat S (h : MeasurableSet A),
      show R A (_ - _)=0 from darkTime S a x,map_zero,map_zero,smul_zero]
  change R A (∫ y, T y)=0
  have hf : Integrable T := travel_integrable S a f x p
  rw [← ContinuousLinearMap.integral_comp_comm _ hf]; simp_rw [he]
  exact integral_zero _ _

lemma wage_paid (t : ℝ≥0) (x : E4) (p : 0 ≤ time x) : ‖wage t x‖ ≤ 1 := by
  rw [wage, show (1:ℂ)- (tinct timeAxis t x:ℂ) = ((1-tinct timeAxis t x:ℝ):ℂ) from (by push_cast; rfl)]
  rw [Complex.norm_real,Real.norm_of_nonneg (sub_nonneg.mpr (fuel t x p))]
  exact sub_le_self _ (show 0 ≤ tinct timeAxis t _ from (Real.exp_pos _).le)

lemma heatSpace_bound (t : ℝ≥0) (y : Full) (x : E4) (p : 0 ≤ time x) :
    ‖heatSpace (bankOf y) t x‖ ≤ 1 := by
  rw [heatSpace,norm_mul,plane_norm,one_mul, Complex.norm_real,
    Real.norm_of_nonneg (show 0 ≤ tinct _ _ _ from (Real.exp_pos _).le)]
  exact fuel t x p

lemma fare_bound (t : ℝ≥0) (y : Full) (x : E4) (p : 0 ≤ time x) : ‖fare t y x‖ ≤ 1 := by
  rw [fare,norm_mul]; exact mul_le_one₀ (heatSpace_bound _ y x p) (norm_nonneg _) (wage_paid _ x p)

lemma fare_base_cont (t : ℝ≥0) : Continuous (uncurry (fare t)) := by
  have hc : Continuous fun x : Full × E4 ↦ ((bankOf x.1).val:E4) :=
    continuous_subtype_val.comp (bank_entire.comp continuous_fst)
  have he : Continuous fun x : Full × E4 ↦ inner ℝ x.2 ((bankOf x.1).val:E4) :=
    continuous_snd.inner hc
  have ht := clock_entire
  unfold uncurry fare heatSpace wage plane tinct
  apply Continuous.mul
  · apply Continuous.mul
    · exact continuous_exp.comp ((Complex.continuous_ofReal.comp he).mul continuous_const)
    fun_prop
  fun_prop

lemma fare_integrable (x : H) (t : ℝ≥0) (f : Full → ℝ) (p : SmoothDensity f) :
    Integrable (fun v : Full × E4 ↦ (f v.1:ℂ)*fare t v.1 v.2)
      (volume.prod (ν x)) := by
  refine Integrable.mono' ((p.smooth.continuous.norm.integrable_of_hasCompactSupport p.compact.norm
    (μ:=(volume:Measure Full))).comp_fst (ν x)) ?_ ?_
  · exact (((Complex.continuous_ofReal.comp p.smooth.continuous).comp continuous_fst).mul
      (fare_base_cont t)).aestronglyMeasurable
  have he : ∀ᵐ v ∂(volume:Measure Full).prod (ν x), 0 ≤ time v.2 :=
    (Measure.ae_prod_iff_ae_ae (show MeasurableSet {v : Full × E4 | 0 ≤ time v.2} from
      (isClosed_le continuous_const (Mink.clock_cont.comp continuous_snd)).measurableSet)).2
        (ae_of_all _ fun _ ↦ S.bright x)
  filter_upwards [he] with i u; rw [norm_mul, Complex.norm_real]
  exact mul_le_of_le_one_right (norm_nonneg _) (fare_bound t _ _ u)

def jointCost (t : ℝ≥0) (f : Full → ℝ) (v : E4) : ℂ := ∫ y, (f y:ℂ)*fare t y v

lemma cost_product (g : ℝ → ℝ) (f : Space → ℝ) (t : ℝ≥0) (v : E4) :
    jointCost t (joined f g) v = (temporal g v:ℂ)*frequencyCost f (L v)*wage t v := by
  let T (a : ℝ) : ℂ := g a*tinct timeAxis a.toNNReal v
  let U (y : Space) := (f y:ℂ)*wavePhase (L v) y
  have he (x : Full) : (joined f g x:ℂ)* fare t x v = T (clock x)*U (trans x)*wage t v := by
    unfold T U joined fare heatSpace
    push_cast
    rw [space_bill]; ring
  unfold jointCost; simp_rw [he]; rw [integral_mul_const,joined_integral]
  congr 2
  unfold temporal T; rw [← integral_complex_ofReal]; apply integral_congr_ae (ae_of_all _ fun i ↦ ?_)
  push_cast; rfl

lemma cost_product_ne {g : ℝ → ℝ} (p : TimeDensity g) (f : Space → ℝ) (t : ℝ≥0) (h : 0<t)
    (v : E4) (q : 0 < time v) (u : frequencyCost f (L v) ≠ 0) :
    jointCost t (joined f g) v≠0 := by
  have ht : tinct timeAxis t v < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos h q))
  have hg : wage t v ≠ 0 := sub_ne_zero_of_ne (by exact_mod_cast (Ne.symm ht.ne))
  rw [cost_product]; exact mul_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr (temporal_pos _ p _).ne') u) hg

variable {D : Set E4} (h : MeasurableSet D)
include h

-- formula with one vector already projected
lemma jointPrice (x : H) (t : ℝ≥0) (f : Full → ℝ) (p : SmoothDensity f) :
    inner ℂ (R D x) (reachVector S t f x) = ∫ w in D, jointCost t f w ∂(ν x) := by
  let k := travelVector S t f x
  let A (y : Full) (v : E4) := (f y:ℂ) * fare t y v
  let μ := (ν x).restrict D
  have he (y : Full) : inner ℂ (R D x) (k y)= ∫ v, A y v ∂μ := by
    let a := (clock y).toNNReal
    let G (b : ℝ≥0) := heatSpace (bankOf y) b
    have hG (r : ℝ≥0) : Integrable (G r) μ := (integrable_const 1).mono'
      (show AEStronglyMeasurable _ _ from (show Continuous (G r) by unfold G heatSpace tinct plane; fun_prop).aestronglyMeasurable)
        ((ae_restrict_of_ae (S.bright x)).mono (fun i u ↦ heatSpace_bound _ y _ u))
    have hv (v) : fare t y v=G a v - G (a+t) v := by unfold G fare heatSpace wage a; rw [tint_add]; push_cast; ring
    change inner ℂ _ ((f y:ℂ) • S.U (bankOf y) (S.E a _))=_
    rw [inner_smul_right,map_sub,map_sub,inner_sub_right, ← ContinuousLinearMap.comp_apply (S.E a),
      ← S.time, pairHeat S h,pairHeat S h]
    unfold A; simp_rw [hv]; rw [integral_const_mul,integral_sub (hG _) (hG _)]
  have ht : Integrable (uncurry A) ((volume:Measure Full).prod μ) :=
    (fare_integrable S x t f p).mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  rw [reachVector,total_inner_right _ _ _ _ (travel_integrable _ _ _ _ p)]
  change (∫ y, inner ℂ _ (k y)) = _
  simp_rw [he]; exact integral_integral_swap ht

/-- Nullity of the smeared projection would already kill the untransported projection.
Use still smaller projections with the same first vector; the price integrates the
nonvanishing multiplier. No assumption that `v` is concentrated in this window. -/
theorem window_detects (x : H) (t : ℝ≥0) (f : Full → ℝ) (p : SmoothDensity f)
    (e : ∀ᵐ y ∂(ν x).restrict D, jointCost t f y≠0) (u : R D x≠0) :
    R D (reachVector S t f x) ≠ 0 := by
  let K := jointCost t f
  let μ := (ν x).restrict D
  let y := reachVector S t f x
  have he : Integrable K μ := (fare_integrable S x t f p).integral_prod_right.restrict
  intro hv
  have ht : K =ᵐ[μ] 0 := by
    refine he.ae_eq_zero_of_forall_setIntegral_eq_zero fun A hA _ ↦ ?_
    unfold μ; rw [Measure.restrict_restrict hA]; unfold K
    let U := A ∩ D
    have hm : MeasurableSet U := hA.inter h
    have hy : R U y = 0 := by
      rw [← smaller (P) h Set.inter_subset_right hm]
      simp only [ContinuousLinearMap.comp_apply,show R D y=0 from hv,map_zero]
    rw [← jointPrice S hm x t f p, slides (P) hm, show R U y = _ from hy, inner_zero_right]
  letI : (ae μ).NeBot := ae_neBot.mpr (fun p ↦ u (((P).null_pair h _).1 (Measure.restrict_eq_zero.mp p)))
  obtain ⟨x,hx,w⟩ := (ht.and e).exists; exact w hx -- need NeBot μ
end YM.MacroSix
#print axioms YM.MacroSix.window_detects

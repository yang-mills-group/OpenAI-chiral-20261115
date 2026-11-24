import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Pointwise
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Riemann payment for compact ground-test quadratures

Plain `(I → ℝ)` with its product Lebesgue volume and max norm. Ceil allocation of
right-closed cells as in `YM/Extraction/Round`, adapted to justify strong Bochner costs
at the actual mesh with ready-to-use `finsum` evaluation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MacroSix.Grid

open Filter Function Finset Metric Set MeasureTheory
open scoped Topology NNReal ENNReal BigOperators

variable {I : Type*} [Fintype I] {E : Type*}

abbrev RealPos (I : Type*) := I → ℝ
abbrev Cell (I : Type*) := I → ℤ
local notation "X" => RealPos I
local notation "J" => Cell I

def place (t : ℝ) (a : J) : X := fun i ↦ (a i:ℝ)*t

def tag (t : ℝ) (x : X) : J := fun i ↦ ⌈x i / t⌉

def region (t : ℝ) (p : J) : Set X := {x | tag t x = p}

lemma place_add (t : ℝ) (a b : J) : place t (a+b)=place t a+place t b := by
  ext i; simp [place,add_mul]

variable (t : ℝ) (h : 0 < t)
include h

lemma region_entry (k : J) (x : X) : x ∈ region t k ↔
    ∀ i, x i ∈ Set.Ioc (((k i:ℝ)-1)*t) ((k i:ℝ)*t) := by
  change (tag t x=k) ↔ _
  rw [funext_iff]
  refine forall_congr' fun i ↦ ?_
  rw [tag, Int.ceil_eq_iff, lt_div_iff₀ h, div_le_iff₀ h]
  -- `rw [tag]` might notation
  rfl

lemma region_isBox (k : J) : region t k = Set.pi Set.univ
    (fun i ↦ Set.Ioc (((k i:ℝ)-1)*t) ((k i:ℝ)*t)) := by
  ext x; simpa using region_entry t h k x

lemma measurable_region (k : J) : MeasurableSet (region t k) := by
  rw [region_isBox t h]; exact MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioc

lemma region_volume (k : J) : volume (region t k) = ENNReal.ofReal (t^Fintype.card I) := by
  rw [region_isBox t h]; change (Measure.pi fun _ : I ↦ volume) _ = _
  rw [Measure.pi_pi]
  have he (x : ℤ) : volume (Set.Ioc (((x:ℝ)-1)*t) ((x:ℝ)*t))= ENNReal.ofReal t := by
    rw [Real.volume_Ioc]; congr 1; ring
  simp_rw [he]; rw [Finset.prod_const, Finset.card_univ, ← ENNReal.ofReal_pow h.le]

lemma region_place (p : J) : place t p ∈ region t p := by
  apply (region_entry t h _ _).mpr
  intro i
  exact ⟨mul_lt_mul_of_pos_right (by linarith) h, le_rfl⟩

lemma distance_tag (x : X) : dist x (place t (tag t x)) ≤ t := by
  apply (dist_pi_le_iff h.le).mpr; intro i
  obtain ⟨p,q⟩ := (region_entry t h (tag t x) x).mp rfl i
  rw [Real.dist_eq, abs_le]; unfold place; constructor <;> linarith

lemma compact_tags {K : Set X} (u : IsCompact K) : (place (I:=I) t ⁻¹' K).Finite := by
  classical
  obtain ⟨b,hb⟩ := u.isBounded.subset_closedBall (0:X)
  let P : Set ℤ := Set.Icc ⌊-b/t⌋ ⌈b/t⌉
  have hf : {k : J | ∀ i, k i ∈ P}.Finite := Set.Finite.pi' (fun _ ↦ Set.finite_Icc _ _)
  refine hf.subset fun x p (i : I) ↦ ?_
  have he : dist (place t x i) ((0:X) i) ≤ b := (dist_le_pi_dist _ _ _).trans (hb p)
  change |place t x i - 0| ≤ b at he -- defs
  rw [sub_zero] at he
  have ht := abs_le.mp he
  have hx : (x i:ℝ) ≥ -b/t := (div_le_iff₀ h).mpr ht.1
  have hy : (x i:ℝ) ≤ b/t := (le_div_iff₀ h).mpr ht.2
  have hp := (Int.floor_le (-b/t)).trans hx
  have hw := hy.trans (Int.le_ceil (b/t))
  exact ⟨by exact_mod_cast hp, by exact_mod_cast hw⟩

lemma finite_tags_of [Zero E] {f : X → E} (p : HasCompactSupport f) :
    (Function.support fun k ↦ f (place t k)).Finite :=
  (compact_tags t h p).subset fun _ y ↦ subset_tsupport f y

section integral
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private lemma booking (k : J) (y : E) : Integrable ((region t k).indicator fun _ ↦ y) := by
  rw [integrable_indicator_iff (measurable_region t h k)]
  exact integrableOn_const (by rw [region_volume t h k]; simp)

private lemma allocation (f : J → E) (p : Finset J) (u : Function.support f ⊆ p) :
    (f ∘ tag t)= fun x : X ↦ ∑ i ∈ p, (region t i).indicator (fun _ ↦ f i) x := by
  classical
  funext x
  by_cases q : tag t x ∈ p
  · rw [Finset.sum_eq_single (tag t x)]
    · exact (Set.indicator_of_mem (show x∈region t (tag t x) from rfl) _).symm
    · intro i _ e; exact Set.indicator_of_notMem (fun p ↦ e (Eq.symm (p : tag t x=i))) _
    simp [q]
  · rw [Finset.sum_eq_zero]
    · exact not_not.mp (fun e ↦ q (u e))
    intro i h; exact Set.indicator_of_notMem (fun p ↦ q (Eq.mpr
      (congrArg (fun k ↦ k∈_) (p : tag t x=i)) h)) _

lemma integrable_step {f : J → E} (u : (Function.support f).Finite) : Integrable (f ∘ tag t) := by
  rw [allocation t h f u.toFinset (by simp)]
  exact integrable_finsetSum _ fun i _ ↦ booking t h i (f i)

lemma step_grid_sum {f : J → E} (u : (Function.support f).Finite) :
    ∫ x : X, f (tag t x) = (t^Fintype.card I) • ∑ᶠ k, f k := by
  let p := u.toFinset
  have hp : Function.support f ⊆ p := by simp [p]
  change (∫ x : X, (f ∘ tag t) x) = _
  rw [allocation t h f p hp, finsum_eq_sum_of_support_subset f hp, smul_sum]
  rw [integral_finsetSum _ (fun i _ ↦ booking t h i (f i))]; refine sum_congr rfl fun i _ ↦ ?_
  rw [integral_indicator (measurable_region t h i), setIntegral_const, measureReal_def,
      region_volume t h, ENNReal.toReal_ofReal (by positivity)]

omit h t
lemma quadrature {δ : ℕ → ℝ} (f : X → E) (hf : Continuous f) (hc : HasCompactSupport f)
    (p : ∀ i, 0 < δ i) (h : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun i ↦ ((δ i)^Fintype.card I) • ∑ᶠ k : J, f (place (δ i) k)) atTop (𝓝 (∫ x, f x)) := by
  obtain ⟨R,hR⟩ := (show IsCompact (tsupport f) from hc).isBounded.subset_closedBall (0:X)
  obtain ⟨C,H⟩ := hf.bounded_above_of_compact_support hc
  -- bigger ball pays δ<1 shifts from actual support
  let A := closedBall (0:X) (R+1)
  let F (i : ℕ) (x : X) := f (place (δ i) (tag (δ i) x))
  let B := A.indicator fun _ ↦ C
  have hC : 0 ≤ C := (norm_nonneg _).trans (H 0)
  have hA : MeasurableSet A := Metric.isClosed_closedBall.measurableSet
  have hB : Integrable B := (integrable_indicator_iff hA).mpr (integrableOn_const
    (isCompact_closedBall _ _ |>.measure_lt_top.ne))
  have ht : Tendsto (fun i ↦ (∫ x, F i x)) atTop (𝓝 (∫ x, f x)) := by
    refine tendsto_integral_filter_of_dominated_convergence B
      (Eventually.of_forall (fun i ↦ (integrable_step (δ i) (p i)
        (finite_tags_of (δ i) (p i) hc)).aestronglyMeasurable)) ?_ hB ?_
    · filter_upwards [h.eventually (gt_mem_nhds zero_lt_one)] with i hi
      refine ae_of_all _ fun x ↦ ?_
      by_cases e : x ∈ A
      · rw [show B x=C from Set.indicator_of_mem e _]; exact H _
      rw [show B x=0 from Set.indicator_of_notMem e _]
      have hz : F i x=0 := by
        by_contra g
        have hy : place (δ i) (tag (δ i) x) ∈ tsupport f := subset_tsupport _ g
        exact e ((dist_triangle x (place (δ i) (tag (δ i) x)) (0:X)).trans
          (by have H := hR hy; rw [mem_closedBall] at H
              have hX := distance_tag (δ i) (p i) x; linarith))
      rw [hz,norm_zero]
    refine ae_of_all _ fun x ↦ hf.continuousAt.tendsto.comp ?_
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ ↦ dist_nonneg) (fun i ↦ (dist_comm _ x).le.trans
      (distance_tag (δ i) (p i) x)) h
  exact ht.congr fun i ↦ step_grid_sum (δ i) (p i) (finite_tags_of (δ i) (p i) hc)
end integral
end YM.MacroSix.Grid
#print axioms YM.MacroSix.Grid.quadrature

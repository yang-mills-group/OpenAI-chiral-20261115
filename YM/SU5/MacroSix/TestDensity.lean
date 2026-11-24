import YM.SU5.MacroSix.StrongQuadrature
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! # Smooth tests and algebra of finite support sums -/
set_option autoImplicit false
noncomputable section
namespace YM.MacroSix
open Function Finset Set Filter MeasureTheory
open scoped Topology NNReal ENNReal InnerProductSpace BigOperators ContDiff

variable {I : Type*} [Fintype I]
/-- Always use real volume in *physical pose* coordinates. -/
structure SmoothDensity (f : (I → ℝ) → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ f
  compact : HasCompactSupport f
  nonneg : ∀ x, 0 ≤ f x
  mass : ∫ x, f x = 1

-- integrate independent weights
abbrev weightKernel {X : Type*} (k : X → X → ℂ) (f g : X → ℝ) (q : X × X) :=
  (f q.1:ℂ) * (g q.2:ℂ) * k q.1 q.2

def independently {X : Type*} [MeasureSpace X] (k : X → X → ℂ) (f g : X → ℝ) : ℂ :=
  ∫ q, weightKernel k f g q

variable (H : Hilbert)

lemma compact_weight {A : Type*} [TopologicalSpace A] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [T2Space A] (f : A → ℝ) (u : HasCompactSupport f) (G : A → E) :
    HasCompactSupport (fun x ↦ (f x:ℂ) • G x) :=
  HasCompactSupport.of_support_subset_isCompact u fun i h ↦ subset_tsupport _ (fun p ↦ h (by
    change ((f i):ℂ) • G i=0
    simp [show f i=0 from p]))



lemma weighted_pair_integrable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopology X] [T2Space X] [LocallyCompactSpace X]
    (μ : Measure X) [IsLocallyFiniteMeasure μ] [SigmaFinite μ] (f g : X → H)
    (hf : Continuous f) (hc : HasCompactSupport f) (hg : Continuous g) (hu : HasCompactSupport g) :
    Integrable (fun x : X × X ↦ inner ℂ (f x.1) (g x.2)) (μ.prod μ) := by
  refine (Continuous.inner (hf.comp continuous_fst) (hg.comp continuous_snd)).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact (IsCompact.prod hc hu) fun i h ↦ ?_
  have he : inner ℂ (f i.1) (g i.2) ≠ 0 := h
  exact ⟨subset_tsupport _ (fun p ↦ he (by rw [show f i.1=0 from p]; simp)),
    subset_tsupport _ (fun p ↦ he (by rw [show g i.2=0 from p]; simp))⟩

lemma weighted_pair {X : Type*} [TopologicalSpace X] [MeasureSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopology X] [T2Space X] [LocallyCompactSpace X]
    [IsLocallyFiniteMeasure (volume:Measure X)] [SigmaFinite (volume:Measure X)] (f g : X → H)
    (k : X → X → ℂ) (a b : X → ℝ) (p : ∀ x, weightKernel k a b x = inner ℂ (f x.1) (g x.2))
    (hf : Continuous f) (hc : HasCompactSupport f) (hg : Continuous g) (hu : HasCompactSupport g) :
    Integrable (weightKernel k a b) ∧ independently k a b = inner ℂ (total H volume f) (total H volume g) := by
  have hi := weighted_pair_integrable H volume f g hf hc hg hu
  simp_rw [independently, show weightKernel k a b = _ from funext p]
  constructor
  · exact hi
  rw [total_pair volume H f g (hf.integrable_of_hasCompactSupport hc) (hg.integrable_of_hasCompactSupport hu)]
  exact integral_prod _ hi

/-- Kernel weighting extends by zero off used poses. -/
lemma weights {X : Type*} (k : X → X → ℂ) (p q : X → ℝ) (f g : X → H)
    (h : ∀ x ∈ Function.support p, ∀ y ∈ Function.support q, k x y = inner ℂ (f x) (g y)) (x y : X) :
    weightKernel k p q (x,y) = inner ℂ ((p x:ℂ) • f x) ((q y:ℂ) • g y) := by
  by_cases e : p x=0
  · simp [weightKernel,e]
  by_cases a : q y=0
  · simp [weightKernel,a]
  unfold weightKernel
  simp only [inner_smul_left,inner_smul_right,Complex.conj_ofReal,h x e y a,mul_assoc, mul_left_comm]

section finite
variable {T R : Type*} (p q : T → ℝ) (d : ℝ)

def finiteTest {R : Type*} [AddCommMonoid R] [Module ℂ R] (F : T → R) : R :=
  (d:ℂ) • ∑ᶠ (i : T), (p i:ℂ) • F i

lemma finiteTest_sum [AddCommMonoid R] [Module ℂ R] (F : T → R) (s : Finset T)
    (h : Function.support p ⊆ s) : finiteTest p d F = (d:ℂ) • ∑ i ∈ s, (p i:ℂ) • F i := by
  rw [finiteTest,finsum_eq_sum_of_support_subset]
  intro k u
  exact h (fun (e : p k=0) ↦ u (by simp [e]))

lemma finiteTest_mem [Semiring R] [Algebra ℂ R] (F : T → R) (h : (Function.support p).Finite)
    (S : Subalgebra ℂ R) (q : ∀ i ∈ Function.support p, F i ∈ S) : finiteTest p d F ∈ S := by
  rw [finiteTest_sum p d F h.toFinset (by simp)]
  exact S.smul_mem (S.sum_mem (fun i e ↦ S.smul_mem (q i (by simpa using e)) _)) _

lemma finiteTest_product [Semiring R] [Algebra ℂ R] (F G : T → R) (L : R →ₗ[ℂ] ℂ)
    (s t : Finset T) (h : Function.support p ⊆ s) (u : Function.support q ⊆ t) :
    L (finiteTest p d F * finiteTest q d G) = (d:ℂ)^2 *
      ∑ i ∈ s, ∑ j ∈ t, (p i:ℂ)*(q j:ℂ)*L (F i*G j) := by
  rw [finiteTest_sum _ _ _ _ h, finiteTest_sum _ _ _ _ u]
  simp [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,sum_mul,mul_sum,map_sum,pow_two,
    mul_assoc]
  rw [sum_comm]; exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring

lemma finiteTest_zero [AddCommMonoid R] [Module ℂ R] (F : T → R) (L : R →ₗ[ℂ] ℂ)
    (h : (Function.support p).Finite) (u : ∀ i ∈ Function.support p, L (F i) = 0) :
    L (finiteTest p d F)=0 := by
  rw [finiteTest_sum _ _ _ h.toFinset (by simp), map_smul,map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [sum_eq_zero,mul_zero]
  intro i v; rw [u i (by simpa using v),mul_zero]

lemma finiteTest_inner (F G : T → H) (s t : Finset T) (h : Function.support p ⊆ s)
    (u : Function.support q ⊆ t) :
    inner ℂ (finiteTest p d F) (finiteTest q d G) = (d:ℂ)^2 *
      ∑ i ∈ s, ∑ j ∈ t, (p i:ℂ)*(q j:ℂ)*inner ℂ (F i) (G j) := by
  rw [finiteTest_sum _ _ _ _ h, finiteTest_sum _ _ _ _ u, inner_smul_left, inner_smul_right,
      sum_inner]
  simp only [inner_smul_right, inner_smul_left,Complex.conj_ofReal,inner_sum,pow_two,mul_assoc,mul_left_comm]

lemma finiteTest_compare [Semiring R] [Algebra ℂ R] (F G : T → R) (L : R →ₗ[ℂ] ℂ)
    (h : (Function.support p).Finite) (u : (Function.support q).Finite) (f g : T → H)
    (v : ∀ i ∈ Function.support p, ∀ j ∈ Function.support q,
      L (F i * G j) = inner ℂ (f i) (g j)) :
    L (finiteTest p d F * finiteTest q d G) = inner ℂ (finiteTest p d f) (finiteTest q d g) := by
  rw [finiteTest_product p q d F G L h.toFinset u.toFinset (by simp) (by simp),
    finiteTest_inner H p q d f g h.toFinset u.toFinset (by simp) (by simp)]
  congr 1
  exact sum_congr rfl fun i a ↦ sum_congr rfl fun j b ↦ by
    rw [v i (by simpa using a) j (by simpa using b)]

end finite
end YM.MacroSix
#print axioms YM.MacroSix.weighted_pair
#print axioms YM.MacroSix.finiteTest_compare

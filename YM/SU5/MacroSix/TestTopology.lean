import YM.SU5.MacroSix.GoodDensities

/-! Perturb also the two tests independently in L¹. Only asks bound of kernel on
ordered supports, entered separately (need not pay arbitrary cross versions). -/
set_option autoImplicit false
noncomputable section
namespace YM.MacroSix
open Function Finset Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal InnerProductSpace BigOperators
variable {I : Type} [Fintype I]
local notation "X" => (I → ℝ)

def discrepancy (f g : X → ℝ) : ℝ := ∫ x, ‖f x-g x‖

variable (K : (I → ℝ) → (I → ℝ) → ℂ) (C : ℝ) (c : 0 ≤ C)

def fieldBound (f g : X → ℝ) : Prop :=
  ∀ x ∈ Function.support f, ∀ y ∈ Function.support g, ‖K x y‖ ≤ C

include c
lemma perturb_price (a b f g : X → ℝ) (p : SmoothDensity a) (q : SmoothDensity b)
    (p' : SmoothDensity f) (q' : SmoothDensity g)
    (hi : Integrable (weightKernel K a b)) (hi' : Integrable (weightKernel K f g))
    (h : fieldBound K C a b) (h' : fieldBound K C f g) :
    dist (independently K a b) (independently K f g) ≤ C * (discrepancy a f + discrepancy b g) := by
  let A(i : X × X) := ‖a i.1-f i.1‖ * b i.2
  let B(i : X × X) := f i.1 * ‖b i.2-g i.2‖
  have ha : Integrable A := (p.integrable.sub p'.integrable).norm.mul_prod q.integrable
  have hb : Integrable B := p'.integrable.mul_prod (q.integrable.sub q'.integrable).norm
  have hA : ∫ x, A x=discrepancy a f := calc
    _ = discrepancy a f * ∫ x, b x := integral_prod_mul _ _
    _ = _ := by rw [q.mass,mul_one]
  have hB : ∫ x, B x=discrepancy b g := calc
    _ = (∫ x, f x) * discrepancy b g := integral_prod_mul _ _
    _ = _ := by rw [p'.mass,one_mul]
  let F := weightKernel K a b
  let G := weightKernel K f g
  have ht (i : X × X) : ‖F i-G i‖ ≤ C*(A i+B i) := by
    let u := K i.1 i.2; let v := jointDensity a b i; let w := jointDensity f g i
    have he : F i-G i=(v-w) • u := by simp [F,G,weightKernel,v,w,u,jointDensity,Complex.real_smul]; ring
    have hp : ‖v-w‖ ≤ A i+B i := by
      rw [show v-w=(a i.1-f i.1)*b i.2+f i.1*(b i.2-g i.2) by unfold v w jointDensity; ring]
      apply (norm_add_le ..).trans_eq
      change ‖(a i.1-f i.1)*b i.2‖ + _ = _
      rw [norm_mul,norm_mul,Real.norm_of_nonneg (q.nonneg _),Real.norm_of_nonneg (p'.nonneg _)]
    rw [he,norm_smul,mul_comm C]
    by_cases e : ‖u‖ ≤ C
    · exact mul_le_mul hp e (norm_nonneg _) ((norm_nonneg _).trans hp)
    have h₀ : v=0 := by
      by_contra t; unfold v jointDensity at t
      exact e (h _ (left_ne_zero_of_mul t) _ (right_ne_zero_of_mul t))
    have h₁ : w=0 := by
      by_contra t; unfold w jointDensity at t
      exact e (h' _ (left_ne_zero_of_mul t) _ (right_ne_zero_of_mul t))
    have hh : 0 ≤ A i+B i := (norm_nonneg _).trans hp
    simp [h₀,h₁,mul_nonneg hh c]
  have he : ∫ x, C*(A x+B x) = C*(discrepancy a f+discrepancy b g) := by
    rw [integral_const_mul,integral_add ha hb,hA,hB]
  change dist (∫ x, F x) (∫ x, G x) ≤ _
  rw [dist_eq_norm,← he,← integral_sub (f:=F) (g:=G) hi hi']
  exact (norm_integral_le_integral_norm _).trans (integral_mono (hi.sub hi').norm
    ((ha.fun_add hb).const_mul C) ht)

lemma costs_limit {α : Type*} (L : Filter α) (a b : α → X → ℝ) (f g : X → ℝ)
    (hi' : Integrable (weightKernel K f g)) (p' : SmoothDensity f) (q' : SmoothDensity g)
    (h' : fieldBound K C f g)
    (p : ∀ᶠ x in L, SmoothDensity (a x) ∧ SmoothDensity (b x) ∧
      Integrable (weightKernel K (a x) (b x)) ∧ fieldBound K C (a x) (b x))
    (t : Tendsto (fun i ↦ discrepancy (a i) f) L (𝓝 0))
    (s : Tendsto (fun i ↦ discrepancy (b i) g) L (𝓝 0)) :
    Tendsto (fun i ↦ independently K (a i) (b i)) L (𝓝 (independently K f g)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have he := (t.add s).const_mul C; rw [zero_add,mul_zero] at he
  exact squeeze_zero' (Eventually.of_forall fun i ↦ dist_nonneg)
    (p.mono fun i ⟨p,q,h,e⟩ ↦ perturb_price K C c _ _ _ _ p q p' q' h hi' e h') he
end YM.MacroSix
#print axioms YM.MacroSix.costs_limit

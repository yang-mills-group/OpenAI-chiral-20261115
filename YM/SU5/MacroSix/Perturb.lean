import YM.SU5.MacroSix.GoodDensities

/-! # Variations of densities

Approach any pre-specified densities in admissible supports with *successful* ones,
even by an affine line converging in every finite C^k cost. Also, any successful
pair with strict gaps can be perturbed a bit, independently (we'll give this even in
L¹, so long as we stay qualified).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MacroSix
open Function Finset Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal InnerProductSpace BigOperators ContDiff
variable {I : Type} [Fintype I] {J : Type*} [Fintype J] [DecidableEq J]
local notation "X" => (I → ℝ)
variable (f g : (I → ℝ) → ℝ)

def rideLine (r : ℝ) : X → ℝ := (1-r) • f+r • g
lemma rideOne : rideLine f g 1 = g := by simp [rideLine]
lemma rideZero : rideLine f g 0 = f := by simp [rideLine]
lemma ride_support (r : ℝ) : tsupport (rideLine f g r) ⊆ tsupport f ∪ tsupport g := by
  apply (tsupport_add ((1-r) • f) (r • g)).trans
  exact Set.union_subset_union (tsupport_smul_subset_right (fun _ ↦ 1-r) f) (tsupport_smul_subset_right (fun _ ↦ r) g)
lemma ride_density (p : SmoothDensity f) (q : SmoothDensity g) (r : ℝ) (hr : r ∈ Set.Icc 0 1) :
    SmoothDensity (rideLine f g r) := by
  unfold rideLine; refine ⟨(contDiff_const.smul p.smooth).add (contDiff_const.smul q.smooth),
    p.compact.smul_left.add q.compact.smul_left,fun x ↦ ?_,?_⟩
  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hr.2) (p.nonneg x)) (mul_nonneg hr.1 (q.nonneg x))
  simp only [Pi.add_apply,Pi.smul_apply, smul_eq_mul]
  rw [integral_add (p.integrable.const_mul _) (q.integrable.const_mul _),integral_const_mul,
    integral_const_mul, p.mass, q.mass]; ring

/-- All orders meet uniform precision (simultaneous over any finite set by eventuality).
Sizes in derivative weights are across the whole space; support stays within the union
of the two fixed compact supports. -/
lemma ride_derivative (p : SmoothDensity f) (q : SmoothDensity g)
    (j : ℕ) (ε : ℝ) (e : 0 < ε) : ∀ᶠ r in 𝓝 (0:ℝ),
      ∀ x : (I→ℝ), ‖iteratedFDeriv ℝ j (rideLine f g r - f) x‖ < ε := by
  have hp : ContDiff ℝ j (g-f) := (q.smooth.sub p.smooth).of_le (mod_cast le_top)
  have he : HasCompactSupport (iteratedFDeriv ℝ j (g-f)) := (q.compact.sub p.compact).iteratedFDeriv _
  obtain ⟨C,H⟩ := hp.continuous_iteratedFDeriv'.bounded_above_of_compact_support he
  have ht : Tendsto (fun r : ℝ ↦ ‖r‖ * C) (𝓝 (0:ℝ)) (𝓝 0) := by
    simpa using (continuousAt_id (x:=(0:ℝ))).norm.tendsto.mul_const C
  filter_upwards [ht.eventually (gt_mem_nhds e)] with r t x
  rw [show rideLine f g r-f=r • (g-f) by unfold rideLine; module,
    iteratedFDeriv_const_smul_apply hp.contDiffAt, norm_smul]
  exact (mul_le_mul_of_nonneg_left (H x) (norm_nonneg _)).trans_lt t

/-- Small along test space lines of every pre-specified order. -/
lemma ride_crests (p : SmoothDensity f) (q : SmoothDensity g) (k : ℕ) (ε : ℝ) (e : 0 < ε) :
    ∀ᶠ r in 𝓝 (0:ℝ), ∀ j ≤ k, ∀ x : X, ‖iteratedFDeriv ℝ j (rideLine f g r - f) x‖ < ε := by
  let C := Finset.range (k+1)
  filter_upwards [C.eventually_all.mpr (fun i _ ↦ ride_derivative f g p q i ε e)] with i H j u x
  exact H j (Finset.mem_range.mpr (by omega)) x

private lemma expandB (K : X → X → ℂ) (t u : X → ℝ) (r : ℝ) :
    weightKernel K (rideLine f g r) (rideLine t u r) =
      fun x ↦ ((1-r:ℝ):ℂ)* (((1-r:ℝ):ℂ) * weightKernel K f t x+(r:ℂ)*weightKernel K f u x)+
             (r:ℂ)* (((1-r:ℝ):ℂ) * weightKernel K g t x+(r:ℂ)*weightKernel K g u x) := by
  ext1 x; unfold weightKernel; simp [rideLine]; ring

variable (A B : Set (I → ℝ)) (K : (I → ℝ) → (I → ℝ) → Matrix J J ℂ)

theorem successfulLines (t u : X → ℝ)
    (hi : ∀ f g, SmoothDensity f → tsupport f ⊆ A → SmoothDensity g → tsupport g ⊆ B →
      ∀ j k, Integrable (weightKernel (fun x y ↦ K x y j k) f g))
    (p : SmoothDensity f) (q : SmoothDensity t) (p' : SmoothDensity g) (q' : SmoothDensity u)
    (pf : tsupport f ⊆ A) (pt : tsupport t ⊆ B) (pg : tsupport g ⊆ A) (pu : tsupport u ⊆ B)
    (h : Success (response K g u)) :
    ∀ᶠ r in 𝓝[>] (0:ℝ), r ≤ 1 ∧ Success (response K (rideLine f g r) (rideLine t u r)) := by
  let G(r) := response K (rideLine f g r) (rideLine t u r)
  have hc (j k : J) (v : ℝ) : AnalyticAt ℝ (fun i ↦ G i j k) v := by
    let K' (x y : X) := K x y j k
    let l (f g) := independently K' f g
    change AnalyticAt ℝ (fun i ↦ l _ _) v
    have he (r : ℝ) : l (rideLine f g r) (rideLine t u r) = ((1-r:ℝ):ℂ) *
          (((1-r:ℝ):ℂ) * l f t + (r:ℂ)*l f u) + (r:ℂ)*(((1-r:ℝ):ℂ)*l g t + (r:ℂ)*l g u) := by
      have h₀₀ : Integrable (weightKernel K' f t) := hi _ _ p pf q pt j k
      have h₀₁ : Integrable (weightKernel K' f u) := hi _ _ p pf q' pu j k
      have h₁₀ : Integrable (weightKernel K' g t) := hi _ _ p' pg q pt j k
      have h₁₁ : Integrable (weightKernel K' g u) := hi _ _ p' pg q' pu j k
      unfold l independently; rw [expandB]; dsimp only; rw [integral_add
        (((h₀₀.const_mul _).fun_add (h₀₁.const_mul _)).const_mul _)
        (((h₁₀.const_mul _).fun_add (h₁₁.const_mul _)).const_mul _),
        integral_const_mul, integral_const_mul, integral_add (h₀₀.const_mul _) (h₀₁.const_mul _),
        integral_add (h₁₀.const_mul _) (h₁₁.const_mul _)]; simp_rw [integral_const_mul]
    simp_rw [he]
    have hf : AnalyticAt ℝ ((↑) : ℝ→ℂ) v := Complex.ofRealCLM.analyticAt _
    push_cast; fun_prop
  have he : ∀ᶠ r in 𝓝[≠] (0:ℝ), (compound (G r)) ≠ 0 := by
    by_contra! g'
    have he : ∃ᶠ i in 𝓝[≠] (0:ℝ), (compound ∘ G) i = (fun _ ↦ 0) i := g'
    have ht := AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
      (fun r _ ↦ compound_analytic G r fun j k ↦ hc j k r)
      analyticOnNhd_const isPreconnected_univ (Set.mem_univ _) he (Set.mem_univ (1:ℝ))
    simp only [Function.comp_apply,G,rideOne] at ht
    exact success_iff.mpr h ht
  filter_upwards [he.filter_mono (nhdsWithin_mono _ (fun x (p : 0<x) ↦
    Set.mem_compl_singleton_iff.mpr p.ne')), eventually_nhdsWithin_of_eventually_nhds
      (ge_mem_nhds (show (0:ℝ)<1 from zero_lt_one))] with r h p
  exact ⟨p,success_iff.mp h⟩
end YM.MacroSix
#print axioms YM.MacroSix.ride_crests
#print axioms YM.MacroSix.successfulLines

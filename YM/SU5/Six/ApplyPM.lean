import YM.SU5.Six.ClosePM
import Mathlib.MeasureTheory.Integral.DominatedConvergence
/-!
# Consequences of the bounded spectral multiplier calculus
-/
set_option autoImplicit false
noncomputable section

namespace YM.Spectral.PVM
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ComplexConjugate ComplexOrder

variable {H : Hilbert} {X : Type*} [MeasurableSpace X]
         {f g : X → ℂ} {T U : H.Op} {P : PVM H X}

lemma pairIntegral_diag (hf : P.Admissible f) (x : H) :
    P.pairIntegral f x x = ∫ w, f w ∂P.diagonal x := by
  obtain ⟨T,h⟩ := hf.exists_represents
  rw [←h.on_pair,h.on_diag]

lemma Represents.comm (h : P.Represents f T) (k : P.Represents g U) : T*U = U*T :=
  (h.mul k).unique (mul_comm g f ▸ k.mul h)
lemma Represents.comm_region (h : P.Represents f T) {A} (hA : MeasurableSet A) :
    T*(P.region A) = (P.region A)*T := h.comm (P.represents_indicator A hA)

lemma Represents.indicator (h : P.Represents f T) {A} (hA : MeasurableSet A) :
    P.Represents (A.indicator f) (P.region A * T) := by
  have he : A.indicator (fun _ => (1:ℂ)) * f = A.indicator f := by
    ext x; by_cases hx : x ∈ A <;> simp [hx]
  exact he ▸ (P.represents_indicator A hA).mul h

lemma Represents.square (h : P.Represents f T) :
    P.Represents (fun w => (↑(‖f w‖^2):ℂ)) (T.adjoint * T) := by
  have he : (fun w => conj (f w)) * f = fun w => (↑(‖f w‖^2):ℂ) := by
    ext w
    change conj (f w) * (f w) = _; rw [mul_comm, Complex.mul_conj,Complex.normSq_eq_norm_sq]
  exact he ▸ h.conjugate.mul h

lemma Represents.alter (h : P.Represents f T) (x : H) {A : Set X} (hA : MeasurableSet A) :
    ↑((P.diagonal (T x)).real A) =
      ∫ w, A.indicator (fun w => (↑(‖f w‖^2):ℂ)) w ∂P.diagonal x := by
  rw [P.at_pair hA, ← ContinuousLinearMap.adjoint_inner_right]
  have he : T.adjoint * (P.region A * T) = P.region A * (T.adjoint * T) := by
    rw [←mul_assoc,h.conjugate.comm_region hA,mul_assoc]
  change inner ℂ x ((T.adjoint * (P.region A * T)) x) = _
  rw [he]; exact (h.square.indicator hA).on_diag x

lemma Represents.norm_sq (h : P.Represents f T) (x : H) :
    ‖T x‖^2 = ∫ w, ‖f w‖^2 ∂P.diagonal x := by
  have hs := h.square.on_diag x
  change inner ℂ x (T.adjoint (T x)) = _ at hs
  rw [ContinuousLinearMap.adjoint_inner_right,inner_self_eq_norm_sq_to_K] at hs
  apply Complex.ofReal_injective
  rw [Complex.ofReal_pow]
  exact hs.trans (integral_ofReal (f:=fun w => ‖f w‖^2))

lemma Represents.mono (h : P.Represents f T) (k : P.Represents g U) (x)
    (he : f ≤ᵐ[P.diagonal x] g) : inner ℂ x (T x) ≤ inner ℂ x (U x) := by
  rw [h.on_diag,k.on_diag]
  exact integral_mono_ae (h.admissible.integrable x) (k.admissible.integrable x) he

lemma Represents.norm_le (h : P.Represents f T) {C : ℝ} (hC : 0 ≤ C) (x : H)
    (he : ∀ᵐ w ∂P.diagonal x, ‖f w‖ ≤ C) : ‖T x‖ ≤ C * ‖x‖ := by
  refine le_of_sq_le_sq ?_ (mul_nonneg hC (norm_nonneg _))
  rw [h.norm_sq, mul_pow, ← show (P.diagonal x).real Set.univ = ‖x‖^2
    by rw [P.same .univ,P.all]; rfl]
  refine le_trans (le_abs_self _) ?_
  exact norm_integral_le_of_norm_le_const (he.mono fun w hw => by
    change ‖‖f w‖ ^ 2‖ ≤ C^2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hw 2)

lemma Represents.tendsto_on {b : ℕ → X → ℂ} {S : ℕ → H.Op}
    (h : P.Represents f T) (hs : ∀ n, P.Represents (b n) (S n)) (x : H) (C : ℝ)
    (hC : ∀ n, ∀ᵐ w ∂P.diagonal x, ‖b n w‖ ≤ C)
    (ht : ∀ᵐ w ∂P.diagonal x, Tendsto (fun n => b n w) atTop (𝓝 (f w))) :
    Tendsto (fun n => S n x) atTop (𝓝 (T x)) := by
  have hD : ∀ᵐ w ∂P.diagonal x, ‖f w‖ ≤ C := by
    filter_upwards [ht,ae_all_iff.2 hC] with w hw hi
    exact le_of_tendsto hw.norm (.of_forall hi)
  let B n w := ‖(b n-f) w‖^2
  have hu : Tendsto (fun n => ∫ w, B n w ∂P.diagonal x) atTop (𝓝 (∫ _w, (0:ℝ) ∂P.diagonal x)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (C+C)^2)
      (fun n => ?_) (integrable_const _) (fun n => ?_) ?_
    · exact ((continuous_id.norm.pow 2).comp_aestronglyMeasurable (((hs n).sub h).admissible.integrable x).1)
    · filter_upwards [hC n,hD] with w hu hv
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le ..).trans (add_le_add hu hv)) _
    filter_upwards [ht] with w hw
    have j := (hw.sub_const (f w)).norm.pow 2
    rw [sub_self,norm_zero,sq,zero_mul] at j
    exact j
  rw [integral_zero] at hu
  have hu := hu.sqrt
  rw [Real.sqrt_zero] at hu
  refine tendsto_iff_norm_sub_tendsto_zero.mpr (hu.congr fun n => ?_)
  change _ = ‖(S n-T) x‖
  exact congrArg Real.sqrt (((hs n).sub h).norm_sq x).symm |>.trans (Real.sqrt_sq (norm_nonneg _))

end YM.Spectral.PVM

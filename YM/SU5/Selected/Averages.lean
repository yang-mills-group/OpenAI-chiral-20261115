import YM.SU5.Selected.Loewner
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
/-!
# A single average of countably many stamps

Use the joint origin, not unit eigenmodes of just heat. This gives one mean
projection (no character-dependent sequence of translations) allowing us to
compute the norms of the invariant parts directly under the spectral integral.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SelectionAnalysis
open Function Filter Topology Set Metric Finset ContinuousLinearMap RCLike
open scoped Topology InnerProductSpace NNReal ENNReal ComplexOrder ComplexConjugate CStarAlgebra

variable {B H : Type*} [CStarAlgebra B]
section average
def weight (k : ℕ) := (1:ℝ)/2/2^k
lemma weight_pos (k : ℕ) : 0 < weight k := by unfold weight; positivity
lemma weight_amount : HasSum weight 1 := hasSum_geometric_two' (1:ℝ)
variable (b : ℕ → B)
abbrev weighted (n : ℕ) : B := ((weight n : ℝ):ℂ) • b n
variable (p : ∀ i, ‖b i‖ ≤ 1)
include p in
lemma payment (i) : ‖weighted b i‖ ≤ weight i := by
  rw [weighted,norm_smul,Complex.norm_real,Real.norm_of_nonneg (weight_pos i).le]; exact mul_le_of_le_one_right (weight_pos i).le (p i)
include p
lemma pays_norm : Summable (fun i => ‖weighted b i‖) := .of_nonneg_of_le (fun _ => norm_nonneg _) (payment b p) weight_amount.summable
lemma pays_weight : Summable (weighted b) := (pays_norm b p).of_norm
omit p
noncomputable def concord : B := ∑' i, weighted b i
include p
lemma concord_shy : ‖concord b‖ ≤ 1 := (norm_tsum_le_tsum_norm (pays_norm b p)).trans (((pays_norm b p).tsum_mono weight_amount.summable (payment b p)).trans_eq weight_amount.tsum_eq)

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H))

local notation "a" => ρ (concord b)
lemma concord_small : ‖a‖ ≤ 1 := (NonUnitalStarAlgHom.norm_apply_le ρ _).trans (concord_shy b p)

lemma place_sum (x : H) : HasSum (fun i => (weight i:ℂ) • (ρ (b i) x)) (a x) := by
  let f : B →L[ℂ] (H →L[ℂ] H) := { ρ.toAlgHom.toLinearMap with cont := map_continuous ρ }
  have ht := (ContinuousLinearMap.apply ℂ H x).hasSum (f.hasSum (pays_weight b p).hasSum)
  simp only [weighted,map_smul] at ht; exact ht -- f.hasSum uses f ∘

abbrev joint : Submodule ℂ H := (ρ (concord b)).eqLocus (1 : H →L[ℂ] H)
lemma mem_joint (x : H) : x ∈ joint b ρ ↔ ∀ i, ρ (b i) x=x := by
  let φ (i) := ρ (b i) x
  change a x=x ↔ ∀i,φ i=x
  have hm := place_sum b p ρ x
  have h (i) : ‖φ i‖≤ ‖x‖ :=
    (ρ (b i)).le_opNorm x |>.trans (mul_le_of_le_one_left (norm_nonneg _) ((NonUnitalStarAlgHom.norm_apply_le ρ _).trans (p i)))
  constructor
  · intro k i
    rw [k] at hm
    let W (i : ℕ) := (inner ℂ x (φ i)).re
    have hv := Complex.reCLM.hasSum ((innerSL ℂ x).hasSum hm)
    have hf : HasSum (fun i=> weight i*W i) (‖x‖^2) := by
      change HasSum (fun i => (inner ℂ x ((weight i:ℂ) • φ i)).re) (Complex.re (inner ℂ x x)) at hv
      simp only [inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, show Complex.re (inner ℂ x x) = ‖x‖^2 from inner_self_eq_norm_sq (𝕜 := ℂ) x] at hv; exact hv
    have hx := (weight_amount.mul_right (‖x‖^2)).sub hf
    simp only [one_mul,sub_self] at hx -- display
    have h' (i : ℕ) : W i ≤ ‖x‖^2 :=
      le_trans ((le_abs_self _).trans (Complex.abs_re_le_norm (inner ℂ x (φ i))))
        ((norm_inner_le_norm ..).trans ((mul_le_mul_of_nonneg_left (h i) (norm_nonneg _)).trans_eq (sq ‖x‖).symm))
    have g : weight i*(‖x‖^2)-weight i*W i≤ 0 := by
      apply le_trans _ (le_of_eq hx.tsum_eq)
      exact hx.summable.le_tsum i fun n _ => sub_nonneg.mpr (mul_le_mul_of_nonneg_left (h' n) (weight_pos n).le)
    apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜:=ℂ) (h i)
    rw [inner_re_symm]
    change W i= _
    exact le_antisymm (h' i) (le_of_mul_le_mul_left (sub_nonpos.mp g) (weight_pos i)) -- direction lemma ?
  intro q
  have hl := (show HasSum (fun i=> (weight i:ℂ) • φ i) _ from hm)
  simp_rw [q] at hl
  have he : HasSum (fun i=> (weight i:ℂ) • x) x := by
    have hv := ((Complex.ofRealCLM.hasSum weight_amount)).smul_const x
    simpa using hv
  exact hl.unique he
omit p in
lemma concord_fixed {x : H} (h : x ∈ joint b ρ) : a x=x := h

end average

section kernel
variable (x : B)
noncomputable def probe (n : ℕ) : B := ((n+1:ℂ)⁻¹) • ∑ i ∈ Finset.range (n+1), x^i
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (u : H)
lemma probes (n : ℕ) : ρ (probe x n) u = birkhoffAverage ℂ (ρ x) _root_.id (n+1) u := by
  simp only [probe,map_smul,map_sum,map_pow,birkhoffAverage,birkhoffSum, Nat.cast_add,Nat.cast_one]
  simp -- tune

omit [CompleteSpace H] in
lemma norm_less_power (x : H →L[ℂ] H) (v : H) (n : ℕ) (hx : ‖x‖ ≤ 1) : ‖(⇑x)^[n] v‖ ≤ ‖v‖ := by
  induction n with
  | zero => exact le_refl _
  | succ n k => rw [Function.iterate_succ_apply']; exact ((le_opNorm ..).trans (mul_le_of_le_one_left (norm_nonneg _) hx)).trans k
lemma probes_le {x : B} (h : ‖x‖ ≤ 1) (n : ℕ) : ‖ρ (probe x n) u‖ ≤ ‖u‖ := by
  rw [probes,birkhoffAverage,birkhoffSum]; simp_rw [norm_smul,_root_.id_eq]
  calc
    _ ≤ ‖(((n+1:ℕ):ℂ))⁻¹‖ * ((n+1:ℕ) • ‖u‖) :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ((sum_le_sum fun i _ => norm_less_power (ρ x) u i ((NonUnitalStarAlgHom.norm_apply_le ρ _).trans h)).trans_eq (by simp))) (norm_nonneg _)
    _ ≤ _ := by rw [norm_inv, Complex.norm_natCast, nsmul_eq_mul,inv_mul_cancel_left₀ (by positivity)]

lemma emerges (b : ℕ → B) (p : ∀i, ‖b i‖ ≤ 1) :
    Tendsto (fun n => ρ (probe (concord b) n) u) atTop (𝓝 ((joint b ρ).starProjection u)) := by
  simp_rw [probes]
  exact ((ρ _).tendsto_birkhoffAverage_orthogonalProjection (concord_small b p ρ) u).comp (tendsto_add_atTop_nat 1)

end kernel
end YM.SelectionAnalysis
#print axioms YM.SelectionAnalysis.mem_joint
#print axioms YM.SelectionAnalysis.emerges

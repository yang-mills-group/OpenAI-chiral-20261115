import YM.SU5.Selected.Fibres
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
/-!
# A spectral integral criterion used with Loewner compression

We include the essential *hypothesis* of a square identity. Not enough to
know the expectations of single observables on Ω: here the integral of the
absolute value squared of the character answers matches the norm of the FULL
projection of each input vector. Bake in a continuous spectral representation.
No new subsequence. Analogous spirit to YM.Phase.Unique (there on abstract
OS continuum selection consumers); here any countable set of stamps, proving
unique joint rather than unique heat.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.SelectionAnalysis
open TopologicalSpace MeasureTheory Function Filter Topology Set Metric Finset UniformSpace
open scoped Topology InnerProductSpace NNReal ENNReal ComplexOrder ComplexConjugate CStarAlgebra

variable {X B H : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [MeasurableSpace X] [CompactSpace X] [BorelSpace X]
  [T2Space X]
  (μ : Measure X) [IsProbabilityMeasure μ]
  (f : X → B →ₚ[ℂ] ℂ) (b : ℕ → B) (p : ∀ i, ‖b i‖ ≤ 1)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (ω : H)
  (hf : ∀ i, VacuumState (f i) b) (hm : ∀ x : B, Continuous (fun i => f i x))
  (hμ : ∀ x : B, ∫ i,f i x ∂μ = inner ℂ ω (ρ x ω))
  (hs : ∀ x : B, ∫ i,(‖f i x‖^2 : ℝ) ∂μ = ‖(joint b ρ).starProjection (ρ x ω)‖^2)

local notation "A" i:max => appear (f i)
local notation "Q" i:max => (f i).gnsStarAlgHom
local notation "D" i:max => joint b (Q i)
local notation "K" i:max x:max => (D i).starProjection x
local notation "w" i:max => (A i) 1
include p hf hm hμ hs

private lemma weight_proj (x:B) : ∀ᵐ i ∂μ, (K i ((A i) x))=f i x • (w i) := by
  let P := (joint b ρ).starProjection
  let G i := (K i ((A i) x)); let L i := ‖G i‖^2
  let v n := probe (concord b) n; let z (i : X) (n) := (Q i) (v n) ((A i) x)
  let α (n : ℕ) := ρ (v n) (ρ x ω); let W(n : ℕ) := v n*x
  have he (n:ℕ) (i) : z i n=(A i) (W n) := fibre_mul (f i) _ _
  let h (n : ℕ) (i : X) := ‖z i n‖^2
  have hm' (x : B) : Integrable (fun i=> f i x) μ := (hm x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp (n : ℕ) : Continuous (h n) ∧ ∫ i,h n i ∂μ=‖α n‖^2 := by
    let a := star (W n) * W n
    have H1 : h n = fun i => (f i a).re := funext fun i => by unfold h; rw [he]; exact (fibre_norm ..).symm
    have hz : α n=ρ (W n) ω := by unfold α W; rw [map_mul]; rfl
    rw [H1]; refine ⟨Complex.continuous_re.comp (hm a),?_⟩
    change ∫ i,RCLike.re (f i a) ∂μ = ‖α n‖^2
    rw [integral_re (𝕜:=ℂ) (hm' a),hμ]; unfold a
    rw [map_mul,map_star,hz]
    change RCLike.re (inner ℂ ω ((ρ (W n)).adjoint (ρ (W n) ω))) = _; rw [ContinuousLinearMap.adjoint_inner_right,inner_self_eq_norm_sq]
  have ht (i:X): Tendsto (fun n => h n i) atTop (𝓝 (L i)) := (emerges (Q i) ((A i) x) b p).norm.pow 2
  let g i := Complex.re (f i (star x*x))
  have hG : Integrable g μ := (hm' (star x*x)).re -- tune
  have hh (n:ℕ) : AEStronglyMeasurable (h n) μ := (hp n).1.aestronglyMeasurable -- sec count X?
  have hr n : ∀ᵐ i ∂μ, ‖h n i‖≤g i := ae_of_all _ fun i => by
    unfold h g
    rw [fibre_norm, Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (probes_le (Q i) _ (concord_shy b p) _) _
  have hl : ∀ᵐ i ∂μ,Tendsto (fun n=>h n i) atTop (𝓝 (L i)) := ae_of_all _ ht
  have hg := tendsto_integral_of_dominated_convergence _ hh hG hr hl
  simp_rw [(hp _).2] at hg
  have hk := tendsto_nhds_unique hg ((emerges ρ (ρ x ω) b p).norm.pow 2)
  let a i := ‖f i x‖^2
  have hL : Integrable L μ := ⟨aestronglyMeasurable_of_tendsto_ae atTop hh hl,
    hasFiniteIntegral_of_dominated_convergence hG.2 hr hl⟩
  have hA : Integrable a μ := ((hm x).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hV (i) : L i-a i=‖G i-f i x • (w i)‖^2 := by
    rw [norm_sub_sq (𝕜:=ℂ),norm_smul, fibre_vacuum _ (hf i).unit_norm,mul_one,inner_smul_right]
    have hx : inner ℂ (w i) (G i)= f i x := ((hf i).project_mean (f i) b p _).trans (fibre_first ..)
    rw [← inner_conj_symm (G i) (w i), hx, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    change _= ‖G i‖^2 - 2* _+_ -- sign formula order?
    unfold L a
    rw [show RCLike.re («K»:=ℂ) (↑(‖f i x‖^2):ℂ)=_ from (show Complex.re (↑(‖f i x‖^2):ℂ)=‖f i x‖^2 from Complex.ofReal_re ..)]; ring
  have he : ∫ i,(L-a) i ∂μ=0 := by simp only [Pi.sub_apply,integral_sub hL hA,hk]; rw [show ∫ i,a i∂μ=_ from hs x,sub_self]
  have h' : ∀ᵐ i ∂μ,L i-a i=0 := (integral_eq_zero_iff_of_nonneg (f:=L-a) (fun i => (show 0≤L i-a i from (hV i).symm ▸ sq_nonneg _)) (hL.sub hA)).1 he
  filter_upwards [h'] with i x
  rw [hV] at x
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp x))

lemma rank_one_almost_everywhere [SeparableSpace B] : ∀ᵐ i ∂μ, SingleGround (f i) b := by
  obtain ⟨x,hx⟩ := exists_dense_seq B
  have hl := ae_all_iff.mpr (fun n : ℕ => weight_proj μ f b p ρ ω hf hm hμ hs (x n))
  filter_upwards [hl] with i H
  intro v hv
  let g (n:ℕ) := (A i) (x n)
  let k := w i; let Z := Submodule.span ℂ {k}
  have Hc : IsClosed (Z : Set (f i).GNS) := show IsClosed (↑(Submodule.span ℂ {k}) : Set (f i).GNS) from Submodule.closed_of_finiteDimensional _
  let L := (D i).starProjection
  suffices v ∈ Z from (Submodule.mem_span_singleton).1 this
  have hh : DenseRange g := (fibre_dense _).comp hx (fibre_cont _)
  rw [← Submodule.starProjection_eq_self_iff.mpr hv]
  exact closure_minimal (s:=Set.range g) (fun x ⟨n,(h : g n=x)⟩ => by
    rw [←h]; exact (Submodule.mem_span_singleton).2 ⟨_,(H n).symm⟩) (Hc.preimage L.continuous) (hh v) -- fun subtype syntax

end YM.SelectionAnalysis
#print axioms YM.SelectionAnalysis.rank_one_almost_everywhere

/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Selected.Where

/-! # A projection estimate over compact Ω-law. General helpers to instantiate DoubleLimit.

There is no assertion dense leg for ANY Tapestry.PreMetric etc. Also see comments Phase.Unique.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 260000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selection
namespace Localization.Canton
open Function Filter Set Analysis OS.Ground MeasureTheory
open scoped Matrix MatrixOrder Topology InnerProductSpace ComplexOrder Classical
variable {X Y : Hilbert} (P : Submodule ℂ (X→L[ℂ] Y)) {B : StarSubalgebra ℂ X.Op}
variable (Ω : X) (Z : Panes ↑B) (hZ : Z.Shines X B.subtype Ω)
attribute [local instance] opCStarAlgebra
lemma lowers (hc:IsClosed (↑B : Set X.Op)) (f : B →⋆ₐ[ℂ] ℂ) (V : Blueprint X Y P B f.toAlgHom.toLinearMap) (U : V.Room) (p : P) : ‖V.bloom U p‖ ≤ ‖p‖ := by
  haveI : IsClosed (↑B : Set X.Op) := hc
  letI := StarSubalgebra.cstarAlgebra B
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [V.norm_bloom_sq]
  have he : (f (V.bond p p)).re≤‖p.val.adjoint.comp p.val‖ := (Complex.re_le_norm _).trans (NonUnitalStarAlgHom.norm_apply_le f _)
  rw [ContinuousLinearMap.norm_adjoint_comp_self,←pow_two] at he; exact he -- check sq lemma order
lemma continuous_bloom (hc:IsClosed (↑B : Set X.Op)) (f : B →⋆ₐ[ℂ] ℂ) (V : Blueprint X Y P B f.toAlgHom.toLinearMap) (U : V.Room) : Continuous (V.bloom U) :=
  ((V.bloom U).mkContinuous 1 (fun i => by rw [one_mul]; exact lowers P hc f V U i)).continuous

include hZ
lemma sees_star_sq (b : B) : (∫ i,‖Z.character i b‖^2 ∂Z.μ)=‖b.val Ω‖^2 := by
  have hi:=hZ.ground (star b*b)
  have h (i): Z.character i (star b*b)=↑(‖Z.character i b‖^2) := by
    rw [map_mul,map_star];change starRingEnd ℂ _ * _=_; rw [mul_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  simp_rw [h,integral_complex_ofReal] at hi
  apply Complex.ofReal_injective; rw [hi,Complex.ofReal_pow]
  exact (ContinuousLinearMap.adjoint_inner_right b.val Ω (b.val Ω)).trans (inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (b.val Ω))
omit hZ in
private lemma standard (H : Hilbert) (x y : H) (z : ℂ) (e : inner ℂ x y=z) (p : ‖x‖=1) :
    ‖y-z • x‖^2=‖y‖^2-‖z‖^2 := by
  rw [norm_sub_sq (𝕜:=ℂ),norm_smul, p,mul_one,inner_smul_right,← inner_conj_symm y,e,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [show ∀ i : ℝ, RCLike.re (K := ℂ) (↑i:ℂ)=i from fun _ => rfl]; ring
lemma narrow (H : Z.X→Hilbert) (a ω : ∀ i : Z.X,H i) (b : B) (ha : Integrable (fun i => ‖a i‖^2) Z.μ)
    (hp : ∀ i, ‖ω i‖=1) (t : ∀ i,inner ℂ (ω i) (a i)=Z.character i b)
    (q : (∫ i,‖a i‖^2 ∂Z.μ)=‖b.val Ω‖^2) :
    ∀ᵐ i ∂Z.μ, a i=(Z.character i b) • (ω i) := by
  haveI := hZ.normalized
  let k (i : Z.X) := ‖a i‖^2- ‖Z.character i b‖^2
  have Hz i : k i = ‖a i-(Z.character i b) • ω i‖^2:= (standard (H i) (ω i) (a i) _ (t i) (hp i)).symm
  have hb : Integrable (fun i=>‖Z.character i b‖^2) Z.μ := ((hZ.weak b).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hf : (∫ i, k i ∂Z.μ)=0 := by unfold k; rw [integral_sub ha hb, q,sees_star_sq Ω Z hZ b,sub_self]
  have he : ∀ᵐ i ∂Z.μ,k i=0:= (integral_eq_zero_iff_of_nonneg (f:= k) (fun i => (Hz i).symm ▸ sq_nonneg _) (ha.sub hb)).1 hf
  filter_upwards [he] with i hi; rw [Hz, sq_eq_zero_iff] at hi; exact sub_eq_zero.mp (norm_eq_zero.mp hi)
omit hZ
lemma stays_is (A : Hilbert) (p : Submodule ℂ A) [p.HasOrthogonalProjection] (x y : A) (e : x∈p) : inner ℂ x (p.starProjection y)=inner ℂ x y := by
  rw [← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr e]
lemma irreducible {A : Hilbert} (p : Submodule ℂ A) [p.HasOrthogonalProjection] (u : A) (e : u∈p)
    {B' : Type} {F : B'→A} (h:DenseRange F) (t:∀ i,p.starProjection (F i)∈Submodule.span ℂ {u}) : p=Submodule.span ℂ {u} := by
  refine le_antisymm ?_ ((Submodule.span_le).mpr (by simp [e] )) -- tune
  intro x t'
  have ht : p.starProjection x∈Submodule.span ℂ {u} := closure_minimal (fun y (i:y∈Set.range F) => by
    obtain ⟨i,rfl⟩ := i; exact t i) ((Submodule.closed_of_finiteDimensional (Submodule.span ℂ {u})).preimage p.starProjection.continuous) (h x)
  rwa [Submodule.starProjection_eq_self_iff.mpr t'] at ht
end Localization.Canton
end YM.CF.Buffered.Afterglow.Tower.Selection

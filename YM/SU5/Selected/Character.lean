import YM.SU5.Selected.GaugeDescent
/-!
# Character choice with mixed margin and reflected-positivity descent

Intermediate selection: no claim here that each character, or the one provided by `excels`,
has itself only one joint vacuum when reconstructed. There are two algebras: even Euclidean
marks of the chiral polarization (`AllTests` carrier), with *axial reflection*, and the
operator norm closed abelian C* algebra B of the joint ground compression. Multiplicativity
and extremality on B is weaker than physical extremality. We do not infer character
multiplicativity on Euclidean marked (connectedness, etc).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (j : Axis) (r : Bool) (C : Arena Y H Q.circuit j 0 r)
local notation "R" => Aurora Y H V Q j r C
local notation "A" => Ark.Ht Y H Q.circuit j 0 r C
local notation "W" => floorV Y H Q.circuit j 0 r C
local notation "F₊" n:max => Tower.Field Y H n j 0 r
local notation "φ" n:max => actor Y H n Q.circuit j 0 r C
local notation "Ω" => seat0 Y H V Q j r C
local notation "π₀" => (R).orthogonalProjectionOnto
local notation "N" n:max => cap Y H V n Q Qc j r C
local notation "Test" => Vacancy.observable (tent Y H) r
local notation "Lab" => Beacon (tent Y H) r

local notation "B" => groundAlgebra Y H V Q Qc j r C
local notation "M" s:max => liftCap Y H V Q Qc j r C s
local notation "P₀" => (R).subtypeL
abbrev CapCharacter := ↑(B) →⋆ₐ[ℂ] ℂ
local notation "Ch" => CapCharacter Y H V Q Qc j r C

def marked (χ : Ch) (s : ℕ) (F : Test) : ℂ := χ ((M s) F)

-- routine spectral facts at vanilla types
private lemma op_eval {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [CompleteSpace X] (S : StarSubalgebra ℂ (X →L[ℂ] X)) (hc : IsClosed (S : Set (X →L[ℂ] X)))
    (χ : S →⋆ₐ[ℂ] ℂ) (x : S) (p : 0 ≤ x.val) : 0 ≤ χ x := by
  have hx : χ x ∈ spectrum ℂ x.val := by
    rw [← StarSubalgebra.spectrum_eq (hS:=hc) (a:=x)]
    exact AlgHom.apply_mem_spectrum χ.toAlgHom _
  exact spectrum_nonneg_of_nonneg p hx

private lemma find_char {X : Type} [CommCStarAlgebra X] (x : X) {e : ℝ}
    (v : 0 ≤ e) (h : e < ‖x‖) : ∃ f : X →⋆ₐ[ℂ] ℂ, e < ‖f x‖ := by
  -- namespace
  -- let D := ↥(WeakDual.characterSpace ℂ X)
  let G : X ≃⋆ₐ[ℂ] C(WeakDual.characterSpace ℂ X,ℂ) := gelfandStarTransform X
  have he : ‖G x‖=‖x‖ := (gelfandTransform_isometry X).norm_map_of_map_zero (map_zero _) x
  by_contra! q
  apply h.not_ge; rw [←he]; exact (ContinuousMap.norm_le _ v).2
    fun i => q ((ContinuousMap.evalStarAlgHom ℂ ℂ i).comp (G : X →⋆ₐ[ℂ] C(WeakDual.characterSpace ℂ X,ℂ)))

include V Q Qc C
lemma char_pos (χ : Ch) (x : B) (p : 0 ≤ x.val) : 0 ≤ χ x :=
  op_eval (B) isClosed_closure χ x p
lemma char_mono (χ : Ch) (x y : B) (p : x.val ≤ y.val) : χ x ≤ χ y := by
  have he : 0 ≤ (y-x).val := sub_nonneg.mpr p
  have hv := char_pos Y H V Q Qc j r C χ (y-x) he
  rw [map_sub] at hv; exact sub_nonneg.mp hv

lemma cap_size (s : ℕ) (F : Test) : ‖E s F.val‖ ≤ ‖(M s) F‖ := by
  rw [←inspected Y H V s Q Qc j r C]
  have ht := ground_normalized Y H V Q j r C
  have he := ((N s) F).le_opNorm Ω
  rw [ht,mul_one] at he
  exact (norm_inner_le_norm (𝕜:=ℂ) ..).trans ((by rw [ht,one_mul]; exact he))

lemma excels (s : ℕ) {e : ℝ} (p : 0 ≤ e) (F : Test) (h : e < ‖E s F.val‖) :
    ∃ χ : Ch, e < ‖marked Y H V Q Qc j r C χ s F‖ := by
  letI := spectrumData Y H V Q Qc j r C
  exact find_char ((M s) F) p (lt_of_lt_of_le h (cap_size Y H V Q Qc j r C s F))

omit V Q Qc C
private lemma sandwich_order (X : Hilbert) (x : X.Op) (U : Submodule ℂ X) [CompleteSpace U] :
    let e : U →L[ℂ] U := U.orthogonalProjectionOnto.comp (x.comp U.subtypeL)
    star e * e ≤ U.orthogonalProjectionOnto.comp ((x.adjoint.comp x).comp U.subtypeL) := by
  let π := U.orthogonalProjectionOnto
  let f := π.comp (x.comp U.subtypeL)
  let g := π.comp ((x.adjoint.comp x).comp U.subtypeL)
  -- via diagonal
  change (g-f.adjoint*f).IsPositive
  apply (ContinuousLinearMap.isPositive_iff_complex _).2; intro v
  have h : inner ℂ ((g-f.adjoint*f) v) v = (↑(‖x v.val‖^2 - ‖π (x v.val)‖^2) : ℂ) := by
    rw [ContinuousLinearMap.sub_apply,inner_sub_left]; change inner ℂ (π _) v - inner ℂ (f.adjoint (f v)) v = _
    unfold π; rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
    change inner ℂ (x.adjoint (x v.val)) v.val - inner ℂ (f.adjoint (f v)) v = _
    rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left]
    simp only [inner_self_eq_norm_sq_to_K,f,π,ContinuousLinearMap.comp_apply,Submodule.subtypeL_apply]
    norm_cast -- tune
  have ht := U.norm_orthogonalProjectionOnto_apply_le (x v.val)
  rw [h]
  change ↑(_) = _ ∧ 0 ≤ (‖x v.val‖^2 - ‖π (x v.val)‖^2)
  exact ⟨rfl,sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) ht 2)⟩

include V Q Qc C
lemma square_cover (s : ℕ) (x : F₊ s) :
    let F := toTest Y H j r s x
    star ((N s) F) * (N s) F ≤ (N s) (composed r (dual Y H j r F) F) := by
  obtain ⟨w,u,p,rfl⟩ := eachField_enters Y H j r s x
  dsimp only
  rw [cap_zero_porch Y H V Q Qc j r C s w u p]
  have hx := cap_sandwich Y H V Q Qc j r C s w w u u p p
  dsimp only at hx; rw [hx]
  exact sandwich_order (A) _ (R)

lemma rp_of_char (χ : Ch) (s : ℕ) (x : F₊ s) :
    let F := toTest Y H j r s x
    let read := marked Y H V Q Qc j r C χ s
    ((‖read F‖^2 : ℝ) : ℂ) ≤ read (composed r (dual Y H j r F) F) := by
  intro F read
  let k := (M s) (composed r (dual Y H j r F) F)
  let v := (M s) F
  have he : χ (star v * v) ≤ χ k := char_mono Y H V Q Qc j r C χ (star v * v) k (square_cover Y H V Q Qc j r C s x)
  change (↑(‖χ v‖^2):ℂ) ≤ χ k
  rw [map_mul,map_star] at he
  exact (le_of_eq (by rw [←Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self]; rfl)).trans he -- tune
end YM.CF.Buffered.Afterglow.Tower.Selection

/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.Ground.Spectrum
/-!
# Analysis helpers working at the general C* space, for use with the Satin displayAlgebra

`representation` proof from generic but private `receives_` in `YM/Ground/Spectrum`. This
acknowledges the proof and importantly marks there is NO use of data on a different OS system.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OS.Ground
open Function Set Filter MeasureTheory Measure Spectral TopologicalSpace WeakDual
open scoped Topology NNReal ENNReal InnerProductSpace BigOperators
theorem representation {A : Type} [CommCStarAlgebra A] (H : Hilbert) (p : A →⋆ₐ[ℂ] H.Op) (w : H) (hw : ‖w‖=1)
    (u : ℕ → A) (hu : DenseRange u) (ht : ∀ i : A, p i w=0 → i=0) : ∃ R : Panes A, R.Shines H p w := by
  classical
  let X := Theta (X := A)
  letI : MetrizableSpace X := tiny u hu
  letI : MetricSpace X := metrizableSpaceMetric X
  letI : MeasurableSpace X := borel _; letI : BorelSpace X := ⟨rfl⟩
  let P : Rep.CC X →⋆ₐ[ℂ] H.Op := p.comp ((gelfandStarTransform A).symm : _ →⋆ₐ[ℂ] _)
  let V : Panes A := { X := X, μ := Rep.sees P w, character := view }
  have hp i : P (gelfandStarTransform A i)=p i := congr_arg p ((gelfandStarTransform A).symm_apply_apply _)
  refine ⟨V,?_,?_,bij,view_cont,mark_cont,?_⟩
  · apply isProbabilityMeasure_iff_real.mpr
    change (Rep.sees P w).real _=1
    rw [Rep.size,hw,one_pow]
  · refine supports H P w ?_
    intro x hx
    obtain ⟨i,rfl⟩ := (gelfandStarTransform A).surjective x
    change P (gelfandStarTransform A i) w=0 at hx; rw [hp] at hx
    change (gelfandStarTransform A i)=0; rw [ht i hx,map_zero]
  intro i
  have h := Rep.pairings P w (gelfandStarTransform A i)
  rw [hp] at h; exact h


-- adjust along isomorphism using *same* points and same measure. no hidden change of integral.
variable {A B : Type} [CStarAlgebra A] [CStarAlgebra B] {H J : Hilbert}
    {p : A →⋆ₐ[ℂ] H.Op} {q : B →⋆ₐ[ℂ] J.Op} {w : H} {w' : J}
namespace Panes
noncomputable def adjust (R : Panes A) (e : B ≃⋆ₐ[ℂ] A) : Panes B :=
  { R with character := fun i => (R.character i).comp e.toStarAlgHom }
lemma Shines.adjusted {R : Panes A} (h : R.Shines H p w) (e : B ≃⋆ₐ[ℂ] A)
    (x : ∀ b, inner ℂ w (p (e b) w) = inner ℂ w' (q b w')) :
    (Panes.adjust R e).Shines J q w' := by
  refine ⟨h.normalized,h.support,⟨?_,?_⟩,?_,fun i => h.weak (e i),fun b => (h.ground (e b)).trans (x b)⟩
  · intro i j p
    apply h.onto.1
    ext b
    obtain ⟨a,rfl⟩ := e.surjective b; exact congrArg (fun z : B →⋆ₐ[ℂ] ℂ => z a) p
  · intro χ
    let f := χ.comp (e.symm.toStarAlgHom); obtain ⟨i,h⟩ := h.onto.2 f
    refine ⟨i,DFunLike.ext _ _ fun a => ?_⟩
    change R.character i (e a)=χ a
    rw [h]; exact congrArg χ (e.symm_apply_apply _)
  exact fun i => open CStarAlgebra in map_continuous _ -- tune
lemma Shines.energyMatch {R : Panes A} (h : R.Shines H p w) (x:A) :
    ∫ i, ‖R.character i x‖^2 ∂R.μ = ‖p x w‖^2 := by
  have he i : R.character i (star x*x)= ↑(‖R.character i x‖^2) := by
    rw [map_mul,map_star]; change starRingEnd ℂ _ * _=_
    rw [mul_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  have ht := h.ground (star x*x); simp_rw [he, integral_complex_ofReal] at ht
  apply Complex.ofReal_injective; rw [ht,map_mul,map_star]
  change inner ℂ w ((p x).adjoint (p x w))=↑(‖p x w‖^2)
  rw [ContinuousLinearMap.adjoint_inner_right,inner_self_eq_norm_sq_to_K]; norm_cast
end Panes
end YM.OS.Ground
#print axioms YM.OS.Ground.Panes.Shines.adjusted
#print axioms YM.OS.Ground.representation

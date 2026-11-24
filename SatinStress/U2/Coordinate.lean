import YM.Work.A07
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Entrywise convergence on our real coordinate spaces

The Section proofs use finite-dimensional vector spaces which may not come with
canonical NormedSpace instances (e.g. finite-dimensional polynomial subspaces).
Don't require those from the eventual caller. When needed one can locally give a
Euclidean structure (without changing the underlying modules).

Separating tests may have ANY index (e.g. those allowed in the scaled position
distributions of (81)); finite minors are selected by the actual rank proofs,
not an extra conditioning premise from the caller. Uses arithmetic/normed space
parts of the primary `YM.Work.A07`; the analogous observation-fit over ℂ is
in `YM.Work.A04` & `YM.Dash`. No estimates on their comparison tables or
physical assumptions used.
-/
namespace SatinStress.U2
open Filter Function
open scoped Topology BigOperators

variable {I J E F G : Type*}
namespace Coord

variable [AddCommGroup E] [Module ℝ E]
abbrev dimension := FiniteDimensional ℝ E

noncomputable section
abbrev Realization (E : Type*) [AddCommGroup E] [Module ℝ E] := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
def realize (E : Type*) [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] : E ≃ₗ[ℝ] Realization E :=
  (Module.finBasis ℝ E).equivFun.trans (WithLp.linearEquiv 2 ℝ _).symm
abbrev norms (E : Type*) [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] : NormedAddCommGroup E :=
  NormedAddCommGroup.induced E (Realization E) (realize E) (realize E).injective
-- the following need to avoid switching add instances. Test reduction.
abbrev metric (E : Type*) [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] : letI := norms E; NormedSpace ℝ E :=
  NormedSpace.induced ℝ E _ (realize E)
abbrev inner (E : Type*) [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] : letI := norms E; InnerProductSpace ℝ E :=
  InnerProductSpace.induced (realize E)
end

-- fixed dual arguments only; using this as unconstrained data is useful even before
-- giving arbitrary norm or Grassmann metric.
def Tends (L : Filter I) (u : I → E) (v : E) : Prop :=
  ∀ f : E →ₗ[ℝ] ℝ, Tendsto (fun i => f (u i)) L (𝓝 (f v))
abbrev applyEntry {L : Filter I} {u : I → E} {v : E} := Tends L u v
-- remove abbrev later
end Coord

section Normed
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {L : Filter I} {u : I → E} {v : E}
lemma Coord.iff_norm : Tends L u v ↔ Tendsto u L (𝓝 v) := by
  refine ⟨fun h => ?_,fun h f => f.continuous_of_finiteDimensional.continuousAt.tendsto.comp h⟩
  let b := (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv
  rw [b.toHomeomorph.isEmbedding.tendsto_nhds_iff]
  exact tendsto_pi_nhds.mpr (fun i => h (((LinearMap.proj i : (Fin (Module.finrank ℝ E) → ℝ) →ₗ[ℝ] ℝ)).comp b.toLinearEquiv.toLinearMap))

-- real variant of YM.Dash.fit_plane
lemma Coord.pointwise_lift [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (f : I → E →ₗ[ℝ] F) (g : E →ₗ[ℝ] F) (e : ∀ x, Tendsto (fun i => f i x) L (𝓝 (g x))) :
    Tendsto (fun i => LinearMap.toContinuousLinearMap (f i)) L (𝓝 (LinearMap.toContinuousLinearMap g)) := by
  let B := Module.finBasis ℝ E
  let Q : (Fin (Module.finrank ℝ E) → F) →ₗ[ℝ] E →L[ℝ] F :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp (B.constr ℝ).toLinearMap
  have he (g : E →ₗ[ℝ] F) : Q (fun i => g (B i)) = LinearMap.toContinuousLinearMap g := by
    apply ContinuousLinearMap.coe_injective; exact B.ext fun i => B.constr_basis ..
  have hp : Tendsto (fun i (j : Fin (Module.finrank ℝ E)) => f i (B j)) L (𝓝 (fun j => g (B j))) :=
    tendsto_pi_nhds.mpr (fun _ => e _)
  have h := Q.continuous_of_finiteDimensional.continuousAt.tendsto.comp hp
  convert h using 1
  · funext i; exact (he _).symm
  rw [he g]

omit [FiniteDimensional ℝ E] in
lemma Coord.joint [NormedAddCommGroup F] [NormedSpace ℝ F] {f : I → E →L[ℝ] F} {g : E →L[ℝ] F}
    (hf : Tendsto f L (𝓝 g)) (h : Tendsto u L (𝓝 v)) : Tendsto (fun i => f i (u i)) L (𝓝 (g v)) :=
  (show Continuous (fun x : (E →L[ℝ] F) × E => x.1 x.2) from continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (hf.prodMk_nhds h)

-- variant of A04.tendsto_of_fitted (primary project), over reals/arbitrary filter
-- need at some points the stronger assertion "there is a limit element" when the
-- destination is a priori unknown. Approach use projection G_leftInverse y independent.
lemma Coord.solve [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : I → E →ₗ[ℝ] F} {g : E →ₗ[ℝ] F} (e : ∀ x, Tendsto (fun i => f i x) L (𝓝 (g x)))
    {l : F →ₗ[ℝ] E} (hl : LeftInverse l g) {y : F}
    (h : Tendsto (fun i => f i (u i)) L (𝓝 y)) : Tendsto u L (𝓝 (l y)) := by
  let A (i : I) := LinearMap.toContinuousLinearMap (l.comp (f i))
  have hA : Tendsto A L (𝓝 (1 : E→L[ℝ] E)) := by
    have he : LinearMap.toContinuousLinearMap (l.comp g) = (1 : E→L[ℝ] E) := ContinuousLinearMap.ext hl
    rw [← he]; exact pointwise_lift (fun i => l.comp (f i)) _ (fun x => l.continuous_of_finiteDimensional.continuousAt.tendsto.comp (e x))
  letI := FiniteDimensional.complete ℝ E
  have hb : Tendsto (fun i => Ring.inverse (A i)) L (𝓝 (1 : E→L[ℝ] E)) := by
    rw [← Ring.inverse_one (E→L[ℝ] E)]; exact (NormedRing.inverse_continuousAt (1 : (E →L[ℝ] E)ˣ)).tendsto.comp hA
  have hv : Tendsto (fun i => A i (u i)) L (𝓝 (l y)) :=
    l.continuous_of_finiteDimensional.continuousAt.tendsto.comp h
  change Tendsto u L (𝓝 ((1 : E→L[ℝ] E) (l y)))
  apply (joint hb hv).congr'
  filter_upwards [hA.eventually (Units.nhds (1 : (E →L[ℝ] E)ˣ))] with i hi
  change (Ring.inverse (A i) * A i) (u i) = u i
  rw [Ring.inverse_mul_cancel _ (show IsUnit _ from hi)]; rfl

end Normed
namespace Coord
variable [AddCommGroup E] [Module ℝ E] {L : Filter I} {u : I → E} {v : E}
variable [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G]
lemma Tends.applyLinear (f : E →ₗ[ℝ] F) (h : Tends L u v) : Tends L (fun i => f (u i)) (f v) := fun l => h (l.comp f)
lemma limit_unique [FiniteDimensional ℝ E] [L.NeBot] {v' : E} (h : Tends L u v) (h' : Tends L u v') : v=v' := by
  letI := norms E; letI := metric E
  exact tendsto_nhds_unique (iff_norm.mp h) (iff_norm.mp h')
lemma Tends.congr' {u' : I → E} (h : Tends L u v) (e : u =ᶠ[L] u') : Tends L u' v :=
  fun f => (h f).congr' (e.mono fun _ he => congr_arg f he)
lemma restrict {L' : Filter I} (h : L' ≤ L) (t : Tends L u v) : Tends L' u v :=
  fun f => (t f).mono_left h
lemma Tends.comp {L' : Filter J} {f : J → I} (t : Tends L u v) (h : Tendsto f L' L) : Tends L' (u ∘ f) v := fun F => (t F).comp h
lemma Tends.neg (h : Tends L u v) : Tends L (-u) (-v) := fun f => by
  simp only [Pi.neg_apply,map_neg]; exact (h f).neg
lemma Tends.add {u' : I → E} {v' : E} (h : Tends L u v) (h' : Tends L u' v') : Tends L (u+u') (v+v') := fun f => by
  simp only [Pi.add_apply,map_add]; exact (h f).add (h' f)
lemma Tends.smul (h : Tends L u v) {f : I → ℝ} {y : ℝ} (e : Tendsto f L (𝓝 y)) :
    Tends L (fun i => f i • u i) (y • v) := fun g => by simpa using! (e.smul (h g))
lemma stationary : Tends L (fun _ => v) v := fun _ => tendsto_const_nhds

/-- Entries of linear (and even curried polynomial when iterated) maps.
Targets don't need norms (for input estimates); when composing require finite dimensions. -/
def Entries (L : Filter I) (A : I → E →ₗ[ℝ] F) (a : E →ₗ[ℝ] F) := ∀ x, Tends L (fun i => A i x) (a x)

section
variable [FiniteDimensional ℝ E]
-- Can prove using sum_repr without norms. also works even for infinite F.
lemma Entries.evolve {A : I → E →ₗ[ℝ] F} {a : E →ₗ[ℝ] F} (h : Entries L A a) (t : Tends L u v) :
    Tends L (fun i => A i (u i)) (a v) := by
  let B := Module.finBasis ℝ E
  intro f
  have he (g : E →ₗ[ℝ] F) (y) : f (g y) = ∑ i : Fin (Module.finrank ℝ E), (B.coord i y : ℝ) * f (g (B i)) := by
    rw [← B.sum_repr y, map_sum, map_sum]; simp [Module.Basis.coord_apply] -- nested sums? nth
  rw [he a v, show (fun i => f (A i (u i))) = (fun i => ∑ j:Fin (Module.finrank ℝ E), (B.coord j (u i) : ℝ) * f (A i (B j))) from funext fun i => he (A i) (u i)]
  exact tendsto_finsetSum _ (fun i _ => (t (B.coord i)).mul (h (B i) f))
lemma recover [FiniteDimensional ℝ F] {A : I → E →ₗ[ℝ] F} {a : E →ₗ[ℝ] F}
    (h : Entries L A a) (t : Tends L (fun i => A i (u i)) (a v)) (e : Injective a) : Tends L u v := by
  letI := norms E; letI := metric E
  letI := norms F; letI := metric F
  obtain ⟨l,hl⟩ := a.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr e)
  have he (x : E) : l (a x)=x := LinearMap.congr_fun hl x
  have ht := solve (fun x => iff_norm.mp (h x)) (show LeftInverse l a from he) (iff_norm.mp t)
  rw [he] at ht; exact iff_norm.mpr ht
lemma recover_exists [FiniteDimensional ℝ F] [L.NeBot] {A : I → E →ₗ[ℝ] F} {a : E →ₗ[ℝ] F} {x : F}
    (h : Entries L A a) (t : Tends L (fun i => A i (u i)) x) (e : Injective a) : ∃ v : E, Tends L u v ∧ a v=x := by
  letI := norms E; letI := metric E; letI := norms F; letI := metric F
  obtain ⟨l,hl⟩ := a.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr e)
  have he (x : E) : l (a x)=x := LinearMap.congr_fun hl x
  have ht := iff_norm.mpr (solve (fun x => iff_norm.mp (h x)) (show LeftInverse l a from he) (iff_norm.mp t))
  exact ⟨_,ht, limit_unique (h.evolve ht) t⟩
lemma eventually_inj [FiniteDimensional ℝ F] {A : I → E →ₗ[ℝ] F} {a : E →ₗ[ℝ] F} (h : Entries L A a) (e : Injective a) :
    ∀ᶠ i in L, Injective (A i) := by
  letI := norms E; letI := metric E; letI := norms F; letI := metric F
  exact (pointwise_lift _ _ (fun x => iff_norm.mp (h x))).eventually
    (ContinuousLinearMap.isOpen_injective.mem_nhds (show Injective (LinearMap.toContinuousLinearMap a) from e))

-- apply to metric vectors of any normed finite F without diam if want through finite_rows PI-local
end
end Coord
end SatinStress.U2

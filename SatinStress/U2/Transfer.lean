import SatinStress.U2.Chain
import SatinStress.U2.Fit
/-!
# Transfer in U2

Use (94) from the *same* free graded-coordinate frames as for the weak comparison.
Here is the linear-analytic kernel of the argument: observations can be tested on any
(possibly infinite) separating set of free prices; the resulting rank bound together
with the distributional derivative identities (`close` here) then gives **exact**
exhaustion in (96). Applies also to chains with Fermi sectors where the kernel dimension
of ordinary divergence need not be the free one.

These are presented in linear maps & convergence/$\epsilon$ in frame coordinates. This
cannot just be applied using the checked Spine as is. Getting even `comparison` about
the positions in the constructed kernels is a physical/point-symbol task. This file
records the exact linear algebra consequences and hypotheses; no ascription of these
hypotheses to a Satin purchase or a claim that `T,V,W` and `T',V',W'` here are actual
symbols without first doing that further work.
-/
namespace SatinStress.U2
open Filter Function
open scoped Topology
open Module (finrank)

variable {T V W Z T' V' W' Z' I J : Type*}
  [AddCommGroup T] [Module ℝ T] [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup Z] [Module ℝ Z] [AddCommGroup T'] [Module ℝ T']
  [AddCommGroup V'] [Module ℝ V'] [AddCommGroup W'] [Module ℝ W']
  [AddCommGroup Z'] [Module ℝ Z'] {L : Filter I}

variable (C : ChainData ℝ T V W Z) (A : ChainData ℝ T' V' W' Z')

/-- One frame scheme, `scale` is the physical length ε entering all of U2/U3
    comparison. Linear isos on the c-real forms of these grades. -/
structure Scaling (T V W T' V' W' I : Type*) [AddCommGroup T] [Module ℝ T] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [AddCommGroup T'] [Module ℝ T'] [AddCommGroup V'] [Module ℝ V']
  [AddCommGroup W'] [Module ℝ W'] (L : Filter I) where
  left (i : I) : T ≃ₗ[ℝ] T'
  right (i : I) : W ≃ₗ[ℝ] W'
  middle (i : I) : V ≃ₗ[ℝ] V'
  scale (i : I) : ℝ
  positive (i : I) : 0 < scale i
  shrinks : Tendsto scale L (𝓝 0)

open Coord
variable (r : Scaling T V W T' V' W' I L)
namespace Scaling

def greek (i : I) : (V×W) ≃ₗ[ℝ] V'×W' := (r.middle i).prodCongr (r.right i)

def hereGrad (i : I) := (r.scale i • (r.middle i).symm.toLinearMap) ∘ₗ A.grad ∘ₗ (r.left i).toLinearMap
def hereDiv (i : I) := (r.scale i • (r.right i).symm.toLinearMap) ∘ₗ A.divg ∘ₗ (r.left i).toLinearMap
@[simp] lemma hereGrad_apply (i : I) (x : T) :
    hereGrad A r i x = r.scale i • (r.middle i).symm (A.grad (r.left i x)) := rfl
@[simp] lemma hereDiv_apply (i : I) (x : T) :
    hereDiv A r i x = r.scale i • (r.right i).symm (A.divg (r.left i x)) := rfl
end Scaling

open Scaling

/-- Remaining U2 linear-analytic inputs. This is **not** assuming a price rank in A.
    Each last-grade test can, e.g., evaluate a derivative after the position-test
    kernel in the free coords and still match the comparison while the last spaces
    Z,Z' themselves needn't identify. `detected` is a property of the **free**
    Wick valuation tests G, which could even be chosen just on outdegree tests of
    (93) that separate that finite rank (see U1 pivots). When using those G in a
    physical application need `comparison`, no claim here that arbitrary such tests
    already have intertwinement with the physical costs.
    Typically the positions used in evaluating `F` will instantiate the hypothesis
    using U1 one-other-field slot, with that field itself in the scaled frame, and
    scale chosen before posing/ext testing those pairs. Different filter i can give
    different i-height prices.

    `grads` & `divgs` use (81)'s comparison on the respective bases incl distribution
    derivatives with indicated scalar factors. Can derive them from separating-value
    convergence via `Coord.fitted`, see `Scaling.viaGrades`. -/
structure CanCompare (G : J → Z →ₗ[ℝ] ℝ) (F : I → J → Z' →ₗ[ℝ] ℝ) : Prop where
  grads : Entries L (hereGrad A r) C.grad
  divgs : Entries L (hereDiv A r) C.divg
  detected (x : V×W) : (∀ j, G j (C.obstruction x) = 0) → C.obstruction x = 0
  comparison (j : J) (x : V×W) : Tendsto (fun i => r.scale i * F i j (A.obstruction (r.greek i x))) L
    (𝓝 (G j (C.obstruction x)))

section Via
variable {iV iW : Type*} [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
/-- One convenient way of buying the matrix-convergence part. `v` and `w` here are
    separating (real) linear tests on the *target grades* in the physical application,
    e.g. 2-point and explicit external plenum-admitting tests with their own scaled
    positions & normalized external symbols (separating in the free case; for A all
    that matters is matching in the limit). **Use the same physical symbols & frame**
    when also taking the derivative tests on the lower-grade inputs. No assertion
    yet such hypothesis on the elected system or of a field distribution
    identity there. -/
lemma Scaling.viaGrades (vA : I → iV → V' →ₗ[ℝ] ℝ) (vF : iV → V →ₗ[ℝ] ℝ)
    (wA : I → iW → W' →ₗ[ℝ] ℝ) (wF : iW → W →ₗ[ℝ] ℝ)
    (v_separates : ∀ x, (∀ j, vF j x = 0) → x=0)
    (w_separates : ∀ x, (∀ j, wF j x = 0) → x=0)
    (v : ∀ j x, Tendsto (fun i => vA i j (r.middle i x)) L (𝓝 (vF j x)))
    (w : ∀ j x, Tendsto (fun i => wA i j (r.right i x)) L (𝓝 (wF j x)))
    (vD : ∀ j x, Tendsto (fun i => r.scale i * vA i j (A.grad (r.left i x))) L (𝓝 (vF j (C.grad x))))
    (wD : ∀ j x, Tendsto (fun i => r.scale i * wA i j (A.divg (r.left i x))) L (𝓝 (wF j (C.divg x)))) :
    Entries L (hereGrad A r) C.grad ∧ Entries L (hereDiv A r) C.divg := by
  constructor
  · intro x
    apply fitted (f:=fun i j => vA i j ∘ₗ (r.middle i).toLinearMap) (g:=vF) v _ v_separates
    intro j; simpa using! vD j x
  intro x
  apply fitted (f:=fun i j => wA i j ∘ₗ (r.right i).toLinearMap) (g:=wF) w _ w_separates
  intro j; simpa using! wD j x

end Via

section Rank
-- can infer actual finite dims from one frame. include inputs for later defeq.
variable {C A r} [FiniteDimensional ℝ T] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    [FiniteDimensional ℝ T'] [FiniteDimensional ℝ V'] [FiniteDimensional ℝ W']
variable {G : J → Z →ₗ[ℝ] ℝ} {F : I → J → Z' →ₗ[ℝ] ℝ}

variable (h : C.Full) (c : CanCompare C A r G F) [L.NeBot]
include h c
omit [FiniteDimensional ℝ T'] [FiniteDimensional ℝ W] [FiniteDimensional ℝ V'] [FiniteDimensional ℝ W'] in
lemma lift_grad : Injective A.grad := by
  obtain ⟨k,hk⟩ := (eventually_inj c.grads h.injective_grad).exists
  intro x y eq
  apply (r.left k).symm.injective; apply hk
  simp [eq]

omit h [FiniteDimensional ℝ V] [FiniteDimensional ℝ V'] [FiniteDimensional ℝ W'] in
lemma lift_divergence : finrank ℝ (C.divg.range) ≤ finrank ℝ (A.divg.range) :=
  lesser_entry c.divgs -- syntactic?

omit h [FiniteDimensional ℝ T] [FiniteDimensional ℝ T'] in
lemma lift_obstruction : finrank ℝ (C.obstruction.range) ≤ finrank ℝ (A.obstruction.range) := by
  apply Confronts.lesser (G:=G) (L:=L) (F:=fun i j => r.scale i • F i j) (u:=fun i => (r.greek i).toLinearMap)
  exact ⟨c.comparison,c.detected⟩

omit [FiniteDimensional ℝ T'] in
lemma exact_at (s : A.Closed) : A.Full := by
  have ht := lift_grad h c
  have hp : Injective A.previous := fun _ _ e => ht (congr_arg Prod.fst e)
  obtain ⟨i⟩ := Filter.nonempty_of_neBot L
  have eT := (r.left i).finrank_eq
  have eW := (r.right i).finrank_eq
  have eV := (r.middle i).finrank_eq
  refine ⟨ht, Submodule.eq_of_le_of_finrank_le (fun q ⟨x,hx⟩ => hx ▸ LinearMap.mem_ker.mpr (s x)) ?_⟩
  have he := LinearMap.finrank_range_add_finrank_ker A.obstruction
  rw [Module.finrank_prod] at he
  rw [LinearMap.finrank_range_of_inj hp]
  have hf := h.count; rw [eT,eV,eW] at hf
  have hz := lift_obstruction c
  omega

omit h [FiniteDimensional ℝ V] [FiniteDimensional ℝ V'] in
theorem conservation_compare : finrank ℝ C.supply + finrank ℝ C.divg.range ≤ finrank ℝ A.supply + finrank ℝ W ∧
    finrank ℝ A.supply ≤ finrank ℝ C.supply := by
  obtain ⟨i⟩ := Filter.nonempty_of_neBot L
  unfold ChainData.supply
  have ht := LinearMap.finrank_range_add_finrank_ker C.divg
  have hf := LinearMap.finrank_range_add_finrank_ker A.divg
  have hu : finrank ℝ A.divg.range ≤ finrank ℝ W' := A.divg.range.finrank_le
  have hx := lift_divergence c
  have eT := (r.left i).finrank_eq
  have eW := (r.right i).finrank_eq
  omega
end Rank
end SatinStress.U2

import SatinStress.U2.Transfer

/-!
# Conserved multiplets induced left product from insertions

On one point hierarchy the slots give an array of variations by Θ. Keep it separate from
any assumption of an algebra of translations. Obtain the bilinear product on the
*actual D kernel supplied by the transfer*, and show commutation of its left multipliers,
**without** assuming associativity or assuming (107).

Here `Insertion` and `Interchange` are still hypotheses; see meanings in MS eqs (87)--(92).
This file is the linear part of that comparison, spelling out the remaining analytic
input (all those equalities must hold on the particular inserted kernels, not just with
respect to a tangent cost).
-/
namespace SatinStress.U2
open Function Module
open scoped Topology

variable {T V W Z : Type*} [AddCommGroup T] [Module ℝ T]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup Z] [Module ℝ Z]
variable (C : ChainData ℝ T V W Z)
namespace ChainData

/-- Results of *first* shell operations (constant-vector translation (87), sampled
in all axes k, as the array of resulting elements in V). U2 drift of T*s uses them
only on T,T ∈ supply. `closed` is bought by differentiating in the slot against all
kernel tests, as T satisfies the `divg` law, not assuming those insertions already
give ∂_k of T. -/
structure Insertion where
  theta : C.supply →ₗ[ℝ] C.supply →ₗ[ℝ] V
  closed (a b) : C.obstruction (theta a b,0) = 0

variable {C} (h : C.Full) (P : C.Insertion)
namespace Insertion

include h
lemma exists_mark (x y : C.supply) : ∃ z : C.supply, C.grad z.val = P.theta x y := by
  obtain ⟨t,hz,-⟩ := h.solves _ (P.closed x y)
  exact ⟨⟨t,LinearMap.mem_ker.mpr (congr_arg Prod.snd hz)⟩,congr_arg Prod.fst hz⟩
 
--!
noncomputable def marked (x y : C.supply) : C.supply := Classical.choose (P.exists_mark h x y)
lemma marked_spec (x y : C.supply) : C.grad (marked h P x y).val = P.theta x y := Classical.choose_spec (P.exists_mark h x y)
lemma eq_mark (x y z : C.supply) (hz : C.grad z.val = P.theta x y) : z = marked h P x y :=
  Subtype.ext (h.injective_grad (hz.trans (marked_spec h P x y).symm))

noncomputable def left (x : C.supply) : C.supply →ₗ[ℝ] C.supply where
  toFun y := marked h P x y
  map_smul' c y := by
    symm; apply eq_mark; simp [marked_spec]
  map_add' y z := by symm; apply eq_mark; simp [marked_spec]
noncomputable def product : C.supply →ₗ[ℝ] C.supply →ₗ[ℝ] C.supply where
  toFun := left h P
  map_smul' c y := by
    ext1 x; change marked h P _ x = c • marked h P y x
    symm; apply eq_mark; simp [marked_spec]
  map_add' y z := by
    ext1 x; change marked h P _ x = marked h P y x + marked h P z x
    symm; apply eq_mark; simp [marked_spec]

/-- Exact symbol action on every member of `supply`. -/
theorem design (x y : C.supply) : C.grad ((P.product h x y).val) = P.theta x y := marked_spec h P x y

section
variable (Y : Type*) [AddCommGroup Y] [Module ℝ Y]
omit h

/-- Remain to prove the analytic identities at the (92) comparisons, and separation
of the second derivatives. Can, for instance, use Y indexed by just the particular
axis k, all component indices and all allowed real-test projections of the prices.

Interpretation of fields:
  - `strain v` is tested `∂_k` on that V array's outer-k component (i.e. takes
    (v_{kij}) and tests all `∂_k v_{kij}` using ∂ purely distributional,
    no sum over k). May keep even one k.
  - `enter a v` is tested `Δ_{e_k}^a v_k` on those same labels as in strain `v`
    against those same kernel tests, by *annular* insertion.
  - `rim c v`: RHS insertion of (92) when `L=e_k`, and external T test `c`,
    but inserting `v` within instead of `theta a b`. The regular tests in this
    slot include only those used in the (92) comparison; with additional
    qualifications if needed for these definitions (e.g., choose cutoffs fixed
    at those prices first; `v` doesn't have to itself be conserved).

So `step` from (88), `difference` from (92), `zero` from conservation for c'
(subscripts (92), integrate by parts), and `determined` from the Wick weak
comparison detecting even `∂_k^2`. No rank hypothesis on a grade-6 symbol space. -/
structure Interchange where
  strain : V →ₗ[ℝ] Y
  enter (a : C.supply) : V →ₗ[ℝ] Y
  rim (c : C.supply) : V →ₗ[ℝ] Y
  step (a c : C.supply) : enter a (C.grad c.val) = strain (P.theta a c)
  difference (a b c : C.supply) :
    enter a (P.theta b c) - enter b (P.theta a c) = rim c (P.theta a b)
  zero (c c' : C.supply) : rim c (C.grad c'.val) = 0
  -- can strengthen using all T outside the supply even
  determined : Injective (fun x : T => strain (C.grad x))
variable {Y}
include h

lemma Interchange.commutes {P : C.Insertion} (H : P.Interchange Y) (x y z : C.supply) :
    P.product h x (P.product h y z) = P.product h y (P.product h x z) := by
  have hv : H.enter x (P.theta y z) - H.enter y (P.theta x z)=0 := by
    rw [H.difference,← P.design h x y,H.zero]
  apply Subtype.ext
  apply H.determined
  change H.strain (C.grad _) = H.strain (C.grad _)
  rw [P.design,P.design,← H.step,← H.step,P.design,P.design]; exact sub_eq_zero.mp hv
end
end Insertion
end ChainData
end SatinStress.U2

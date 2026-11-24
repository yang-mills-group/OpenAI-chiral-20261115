import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.Complex.Basic
/-!
# Raw signed monomial slots in the U1 certificate

This is for the *complexified class computation*, `the construction notes` pp headed
U1. Once one gets to the finite g/f/x calculation (in particular *after* the Flavor /
SU reduction), the raw monomial labels have a very simple monomial representation of
signed permutations of the **four coordinate axes**.
No on-shell relations are put on the slots in this file.

The generating reflections used in the orbit computation are the independent coordinate
sign flips, and we also impose covariance for all ordinary permutations.
`Slot.inds` and `Slot.detPower` mean that flipping axis `i` acts by the sign
`(-1)^(inds.count i + detPower)`. `factor` is the sign for an ordinary permutation
(*including* its determinant to the relevant power). We put tensor index slots together
with field slots, so e.g. an equivariant tensor **before quotient** has an invariant
array of coefficients in the combined slot. Store only sorted symmetric pairs, as
in the MS; later linear maps such as divergence will **read** both `ij` and `ji`
components using this same indexing, no sqrt-2 factors.
-/

namespace SatinStress.U1

open List
abbrev Axis := Fin 4
abbrev Motion := Equiv.Perm Axis

def axes : List Axis := [0,1,2,3]
@[simp]
theorem mem_axes (i : Axis) : i ∈ axes := by decide +revert

def sgn (p : Motion) : ℤˣ := Equiv.Perm.signAux2 axes p
lemma sgn_eq (p : Motion) : sgn p = Equiv.Perm.signAux p := by
  simpa [sgn] using
    (Equiv.Perm.signAux_eq_signAux2 axes p (Equiv.refl _) (by simp)).symm
lemma sgn_sign (p : Motion) : sgn p = Equiv.Perm.sign p := by
  rw [sgn_eq]
  induction p using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul p x y h ih =>
    rw [Equiv.Perm.signAux_mul, map_mul, Equiv.Perm.signAux_swap h, Equiv.Perm.sign_swap h, ih]
@[simp] lemma sgn_id : sgn (1 : Motion) = 1 := by simp [sgn_sign]
@[simp] lemma sgn_mul (p q : Motion) : sgn (p * q) = sgn p * sgn q := by
  simp only [sgn_sign, map_mul]

-- Use a definite enumeration. Avoid depending on evaluating Classical Equiv machinery.
-- Insert a coordinate at a time by swaps. Order inside an orbit won't matter.
def motions : List Motion :=
  axes.flatMap fun a => ([1,2,3] : List Axis).flatMap fun b =>
    ([2,3] : List Axis).map fun c => Equiv.swap 0 a * Equiv.swap 1 b * Equiv.swap 2 c
lemma motions_nodup : motions.Nodup := by decide +kernel
lemma mem_motions (p : Motion) : p ∈ motions := by
  classical
  -- card = 4!
  have h : motions.toFinset = Finset.univ := Finset.eq_of_subset_of_card_le
    (Finset.subset_univ _) (by
      rw [List.toFinset_card_of_nodup motions_nodup, Finset.card_univ,
          Fintype.card_perm, Fintype.card_fin]; decide)
  exact List.mem_toFinset.mp (by rw [h]; apply Finset.mem_univ)

/-- Only orthogonal signed-permutation kinematics, including an axis list
on each monomial by which independent sign flips act, with determinant twist.
The sign-bit test does not need the full signed group multiplication implementation. -/
structure Slot (α : Type) where
  mv : Motion → α → α
  mv_id : ∀ x, mv 1 x = x
  mv_mul : ∀ p q x, mv (p * q) x = mv p (mv q x)
  factor : Motion → α → ℤˣ
  factor_id : ∀ x, factor 1 x = 1
  factor_mul : ∀ p q x, factor (p*q) x = factor p (mv q x) * factor q x
  inds : α → List Axis
  inds_mv : ∀ p a, List.Perm (inds (mv p a)) ((inds a).map p)
  detPower : α → ℕ
  detPower_mv : ∀ p a, detPower (mv p a) = detPower a
attribute [simp] Slot.mv_id Slot.mv_mul Slot.factor_id Slot.factor_mul Slot.detPower_mv

namespace Slot
variable {α β : Type}

def mvEquiv (S : Slot α) (p : Motion) : Equiv.Perm α where
  toFun := S.mv p
  invFun := S.mv p⁻¹
  left_inv a := by rw [← mv_mul]; simp
  right_inv a := by rw [← mv_mul]; simp
lemma mv_inj (S : Slot α) (p : Motion) : Function.Injective (S.mv p) :=
  (mvEquiv S p).injective

@[simps]
def unit : Slot Unit where
  mv _ := id
  mv_id _ := rfl
  mv_mul _ _ _ := rfl
  factor _ _ := 1
  factor_id _ := rfl
  factor_mul _ _ _ := (one_mul 1).symm
  inds _ := []
  inds_mv _ _ := by simp
  detPower _ := 0
  detPower_mv _ _ := rfl
@[simps]
def void : Slot Empty where
  mv _ := id
  mv_id _ := rfl
  mv_mul _ _ _ := rfl
  factor _ _ := 1
  factor_id _ := rfl
  factor_mul _ _ _ := (one_mul 1).symm
  inds _ := []
  inds_mv _ _ := by simp
  detPower _ := 0
  detPower_mv _ _ := rfl

@[simps]
def vector : Slot Axis where
  mv p i := p i
  mv_id _ := rfl
  mv_mul _ _ _ := rfl
  factor _ _ := 1
  factor_id _ := rfl
  factor_mul _ _ _ := (one_mul 1).symm
  inds i := [i]
  inds_mv _ _ := by simp
  detPower _ := 0
  detPower_mv _ _ := rfl
/-- Increases the power of the extra determinant by one (twists by `sign`
on permutations and also changes parity for each sign flip). -/
@[simps]
def twist (S : Slot α) : Slot α where
  mv := S.mv
  mv_id := S.mv_id
  mv_mul := S.mv_mul
  inds := S.inds
  inds_mv := S.inds_mv
  factor p x := sgn p * S.factor p x
  factor_id x := by simp
  factor_mul p q x := by simp; ac_rfl
  detPower x := S.detPower x + 1
  detPower_mv p x := by simp

@[simps]
def prod (S : Slot α) (T : Slot β) : Slot (α × β) where
  mv p ab := (S.mv p ab.1, T.mv p ab.2)
  mv_id _ := by simp
  mv_mul _ _ _ := by simp
  factor p x := S.factor p x.1 * T.factor p x.2
  factor_id x := by simp
  factor_mul p q x := by simp; ac_rfl
  inds x := S.inds x.1 ++ T.inds x.2
  inds_mv p x := by simp only [map_append]; exact (S.inds_mv p x.1).append (T.inds_mv p x.2)
  detPower x := S.detPower x.1 + T.detPower x.2
  detPower_mv p x := by simp

@[simps]
def sum (S : Slot α) (T : Slot β) : Slot (α ⊕ β) where
  mv p := Sum.map (S.mv p) (T.mv p)
  mv_id x := by cases x <;> simp
  mv_mul p q x := by cases x <;> simp
  factor p := Sum.elim (S.factor p) (T.factor p)
  factor_id x := by cases x <;> simp
  factor_mul p q x := by cases x <;> simp
  inds := Sum.elim S.inds T.inds
  inds_mv p x := by cases x <;> simp [S.inds_mv,T.inds_mv]
  detPower := Sum.elim S.detPower T.detPower
  detPower_mv p x := by cases x <;> simp
end Slot
end SatinStress.U1

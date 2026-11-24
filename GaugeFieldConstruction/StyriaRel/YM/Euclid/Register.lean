/- This file incorporates modified third-party source. See the source attributions in notices/. -/ -- Adapted/namespace-shifted from repository YM.Euclid.Register (parametric register)
import YM.Labels.Reference

/-!
# Common reference coordinates

The same in extraction and in reconstruction of a particular hierarchy.
-/
set_option autoImplicit false
noncomputable section
namespace YM.NSF
open Labels
open scoped Topology BigOperators

abbrev Gauge := Unit

structure Register (G : Gauge) where
  dim : ℕ→ℕ
  scalar (d : ℕ) : Fin (dim d) → ℂ
  mirrorGroup (d : ℕ) (s : Signed) : (Fin (dim d) → ℂ) →ₗ[ℂ] (Fin (dim d) → ℂ)
  bar_scalar (d) : star (scalar d) = scalar d
  mirror_scalar (s : Signed) (d : ℕ) : mirrorGroup d s (scalar d) = scalar d
  mirror_mul (s q : Signed) (d : ℕ) (v : Fin (dim d)→ℂ) :
    mirrorGroup d (s*q) v = mirrorGroup d s (mirrorGroup d q v)
  mirror_one (d : ℕ) (v : Fin (dim d)→ℂ) : mirrorGroup d 1 v = v
  star_mirror (s : Signed) (d : ℕ) (v : Fin (dim d)→ℂ) :
    star (mirrorGroup d s v) = mirrorGroup d s (star v)

attribute [simp] Register.bar_scalar Register.mirror_scalar Register.mirror_mul Register.mirror_one Register.star_mirror
namespace Register
variable {G : Gauge} (L : Register G)

abbrev Ref (d : ℕ) := Fin (L.dim d)→ℂ

def bar (d : ℕ) : L.Ref d →ₛₗ[starRingEnd ℂ] L.Ref d where
  toFun p := star p
  map_add' p q := star_add p q
  map_smul' r p := star_smul r p

@[simp] theorem bar_apply (d) (x : L.Ref d) : L.bar d x = star x := rfl

/-- Reflection adjoint at coordinate through 0. Use `bar` alone for ordinary complexification, Euclidean real label conventions. -/
def adj (d : ℕ) (a : Axis) : L.Ref d →ₛₗ[starRingEnd ℂ] L.Ref d :=
  (L.mirrorGroup d (Signed.mirror a)).comp (L.bar d)

@[simp] theorem adj_scalar (d a) : L.adj d a (L.scalar d) = L.scalar d := by
  simp only [adj,LinearMap.comp_apply,bar_apply,bar_scalar,mirror_scalar]

@[simp] theorem reflected (d a) (v : L.Ref d) : L.adj d a (L.adj d a v) = v := by
  simp only [adj,LinearMap.comp_apply,bar_apply,star_mirror, star_star]
  rw [← mirror_mul, show Signed.mirror a * Signed.mirror a = 1 from
    calc
      _ = (Signed.mirror a)⁻¹ * Signed.mirror a := rfl
      _ = _ := inv_mul_cancel _, mirror_one]

/-- Reference label carrying its own weight. Works across arities with no casts
until reading a slot. -/
abbrev Token := (d : ℕ) × L.Ref d

def one (d : ℕ) : L.Token := ⟨d,L.scalar d⟩
def move (s : Signed) (x : L.Token) : L.Token := ⟨x.1,L.mirrorGroup x.1 s x.2⟩
def conjugate (x : L.Token) : L.Token := ⟨x.1,star x.2⟩
def reflectedToken (a : Axis) (x : L.Token) : L.Token := ⟨x.1,L.adj x.1 a x.2⟩

@[simp] theorem token_adjoint (a : Axis) (x : L.Token) : L.move (Signed.mirror a) (L.conjugate x) = L.reflectedToken a x := rfl
end Register
end YM.NSF

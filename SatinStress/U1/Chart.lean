import SatinStress.U1.Sparse
import SatinStress.U1.Lab
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Span.Defs
/-!
# Null-coordinate chart in U1

After splitting types g/f/x (pure GE with color product, pure PH, Mixed). Polynomials
as specified near (93). Coordinate of an ordinary derivative is multiplication by the
sum of the momenta, *including* the third momentum for Mixed. Lie/cube labels share
the same Axis.

Define an invariant image space with **real or complex coefficients**. Even the rank
statements over ℝ will be about that space (evaluation against all complex variables
as polynomials, with the given spin/unit and two curl polarizations where applicable).
Use `Class.image` as the spaces to be analyzed, and `Class.bake` giving exactly the
integer starting arrays for the certificate.
-/

namespace SatinStress.U1
open Finset Radix
open scoped BigOperators Matrix
namespace Chart

def io : Expr := .con ⟨0,1⟩
/-- order l A B l' A' B' l'' A'' B'' -/
def l : Fin 3 → Expr := ![.var 0,.var 3,.var 6]
def A : Fin 3 → Expr := ![.var 1,.var 4,.var 7]
def B : Fin 3 → Expr := ![.var 2,.var 5,.var 8]
/-- null momentum in this chart -/
def P (i : Fin 3) (k : Axis) : Expr := l i *
  ![io * (B i + A i), A i - B i, io * (1 - A i * B i), 1 + A i * B i] k
/-- `partial_A`, `partial_B` directions in the quadric -/
def w (i : Fin 3) (pol : Fin 2) (k : Axis) : Expr := l i * if pol = 0 then
  ![io, (1 : Expr), -(io * B i), B i] k else ![io, (-1 : Expr), -(io * A i), A i] k
def F (i : Fin 3) (pol : Fin 2) (j k : Axis) : Expr :=
  P i j * w i pol k - P i k * w i pol j
def blade (i : Fin 3) (pol : Fin 2) (b : Blade) := F i pol b.val.1 b.val.2
/-- `U H_i V'` on the C and R legs (`H`, i and block conventions of U1);
U=(-A,1), V'=(-B',1)ᵀ. -/
def spin (i : Axis) : Expr := let a := A 0; let b := B 1
  ![io * (a+b), a-b, io*(1-a*b), a*b+1] i
  -- Check! H0[[0,-i],[-i,0]] ok; H1; H2; H3

def s (k : Axis) := P 0 k + P 1 k
def d (k : Axis) := P 1 k - P 0 k
def t (k : Axis) := s k + P 2 k

end Chart

-- A table of polynomials, row order conveniently `(polarizations, external tensor argument)`.
-- Polar types T and V (the ij's) already store just the sorted coordinates.
abbrev Grid (row : Type) := row → Many
abbrev Raw (row : Type) := row → Expr
namespace Raw
variable {row : Type}
noncomputable def denote (p : Raw row) : Grid row := fun x => (p x).den
end Raw

/-- The data for evaluation of a homogeneous class, *before* taking any invariant
matrix elements. `mono z b` is the momentum polynomial for the monomial labelled b
at the choice of polarizations z. -/
structure Class (pol m : Type) where
  M : Schedule m
  mono : pol → m → Expr

namespace Class
open Chart

def TT := Schedule.TT
def W := Schedule.W
def V := Schedule.V
abbrev GPol := Fin 2 × Fin 2
abbrev FPol := Unit -- annihilator lines already parameterized, no additional polarization
abbrev XPol := Fin 2

def ge4 : Class GPol G4 where
  M := Schedule.g4
  mono z x := let a := x.val.1; let b := x.val.2
              blade 0 z.1 a * blade 1 z.2 b + blade 1 z.2 a * blade 0 z.1 b

def ge5 : Class GPol G5 where
  M := Schedule.g5
  mono z x := let a := x.1; let b := x.2.1; let k := x.2.2
              blade 0 z.1 a * blade 1 z.2 b * P 1 k + blade 1 z.2 a * blade 0 z.1 b * P 0 k

def ph3 : Class FPol F3 where
  M := Schedule.f3
  mono _ x := spin x

def ph4 : Class FPol F4 where
  M := Schedule.f4
  mono _ x := spin x.1 * (Sum.elim d s x.2) -- L' in inl

def ph5 : Class FPol F5 where
  M := Schedule.f5
  mono _ x := spin x.1 * (match x.2 with
    | .inl a => d a.val.1 * d a.val.2
    | .inr (.inl a) => s a.1 * d a.2
    | .inr (.inr a) => s a.val.1 * s a.val.2)

def mixed4 : Class XPol Empty where
  M := Schedule.void
  mono _ e := e.elim

def mixed : Class XPol X5 where
  M := Schedule.x5
  mono z x := spin x.1 * blade 2 z x.2

variable {pol m o : Type} (C : Class pol m)

open Expr
/-- One entry in the column after projection to row `qr` of the polynomial charts. -/
def singleE [DecidableEq o] (ij : m × o) (k : ℤ) (qr : pol × o) : Expr :=
  if ij.2 = qr.2 then conZ k * C.mono qr.1 ij.1 else 0

def rowE [DecidableEq o] (pieces : List ((m × o) × ℤ)) (qr : pol × o) : Expr :=
  pieces.foldr (fun w p => C.singleE w.1 w.2 qr + p) 0

/-- A projected starting column -/
def column [DecidableEq m] [DecidableEq o] (O : Schedule o) (r : m × o) : Raw (pol × o) :=
  rowE C ((C.M.frame O).toSlot.pieces r)

def bake [DecidableEq m] [DecidableEq o] (O : Schedule o) :=
  (C.M.issuers O).map (C.column O)

variable [Fintype m]
/-- Evaluate *any* raw coefficient array (over field K, for K=ℝ or ℂ) on the charts -/
noncomputable def evaluate (K : Type*) [Field K] [Algebra K ℂ] (o : Type) :
    (m × o → K) →ₗ[K] Grid (pol × o) where
  toFun f z := ∑ a, MvPolynomial.C (algebraMap K ℂ (f (a,z.2))) * Expr.den (C.mono z.1 a)
  map_add' f g := by ext1 z; simp [add_mul, Finset.sum_add_distrib]
  map_smul' u f := by
    ext1 z
    simp [mul_assoc,mul_sum,Algebra.smul_def]
-- is scalar via K-algebra on Many? mathlib tower?

/-- Space of (93) projected raw arrays, i.e., modulo *the polynomial evaluations on
these null charts*; not claiming this definition imposes any Wick-matrix Schwinger
value identity. -/
noncomputable def image (O : Schedule o) (K : Type*) [Field K] [Algebra K ℂ] :
    Submodule K (Grid (pol × o)) :=
  ((C.M.frame O).toSlot.invariant K).map (C.evaluate K o)

omit [Fintype m] in
lemma singleE_at [DecidableEq o] (ij : m × o) (k : ℤ) (qr : pol × o) : den (C.singleE ij k qr) =
    if ij.2 = qr.2 then (k : Many) * den (C.mono qr.1 ij.1) else 0 := by unfold singleE; split <;> simp
omit [Fintype m] in
lemma rowE_at [DecidableEq o] (ps : List ((m × o) × ℤ)) (qr : pol × o) :
    den (C.rowE ps qr) = (ps.map (fun w => den (C.singleE w.1 w.2 qr))).sum := by
  induction ps with
  | nil => simp [rowE]
  | cons a as ih => simpa [rowE] using ih

variable [DecidableEq m] [DecidableEq o] (K : Type*) [Field K] [Algebra K ℂ] [Fintype o]

lemma column_calculation (O : Schedule o) (r : m × o) : Raw.denote (C.column O r) =
    C.evaluate K o ((C.M.frame O).toSlot.column K r) := by
  ext1 z
  let S := (C.M.frame O).toSlot
  let f (a : m × o) := Expr.den (C.singleE a (S.weight r a) z)
  calc
    _ = ((S.locations r).map f).sum := by
      unfold Raw.denote column; rw [rowE_at]; simp only [Slot.pieces,List.map_map]; rfl
    _ = ∑ a ∈ (S.locations r).toFinset, f a := by
      exact (List.sum_toFinset f (List.nodup_dedup _)).symm
    _ = ∑ a, f a := sum_subset (subset_univ _) (fun x _ hx => by
      dsimp only [f]; rw [singleE_at, S.weight_else (by simpa using hx)]; split <;> simp)
    _ = _ := by simp [Fintype.sum_prod_type, f,singleE_at,Class.evaluate, Slot.column]; rfl
lemma currency [CharZero K] (O : Schedule o) :
    C.image O K = Submodule.span K { x | x ∈ (C.bake O).map Raw.denote } := by
  rw [image, Slot.span_columns _ _ _ ((C.M.frame O).all) ((C.M.frame O).key),Submodule.map_span, Set.image_image]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq,bake, List.map_map, List.mem_map, Function.comp_apply,column_calculation C K O]
  rfl
end Class
end SatinStress.U1

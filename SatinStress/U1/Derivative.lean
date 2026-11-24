import SatinStress.U1.CheckRanks

namespace SatinStress.U1
open Radix Finset
open scoped BigOperators

/-!
`Freq` are the arrays of total momentum used on each grade. They are the same
for every polynomial reading in the given row type, i.e. no changing with
polarization. Use *full sums* over `Fin 4` treating symmetric tensor components
with both poses. `divT`, `gradT`, `traceT`, `gradW`, `divV` and (93) will be
true linear maps (only on these polynomial symbol costs). No derivative of Wick
field distributions is asserted here.
-/
namespace Derivative

abbrev Freq := Axis → Expr
abbrev TR (pol : Type) := pol × Sy
abbrev VR (pol : Type) := pol × VSy
abbrev WR (pol : Type) := pol × Axis
abbrev DR (pol : Type) := pol × Axis × Axis

variable (K : Type*) [Field K] [Algebra K ℂ] {pol : Type} (s : Freq)

-- momentum multiplier in any fixed direction.
noncomputable def deriv (i : Axis) {q : Type} : Grid q →ₗ[K] Grid q where
  toFun x z := (s i).den * x z
  map_add' _ _ := by ext1; simp [mul_add]
  map_smul' _ _ := by ext1; simp [Algebra.smul_def,mul_left_comm]
@[simp] lemma deriv_apply (i : Axis) {q : Type} (x : Grid q) (z : q) : deriv K s i x z = (s i).den * x z := rfl
lemma injective (i : Axis) (h : (s i).den ≠ 0) (q : Type) : Function.Injective (deriv K s i (q:=q)) := fun _ _ e =>
  funext fun z => mul_left_cancel₀ h (congr_fun e z)
lemma commute (i j : Axis) {q : Type} (x : Grid q) : deriv K s i (deriv K s j x)=deriv K s j (deriv K s i x) :=
  funext fun _ => mul_left_comm ..

noncomputable def traceT : Grid (TR pol) →ₗ[K] Grid (pol × Unit) where
  toFun x z := ∑ i : Axis, x (z.1,Duo.sym i i)
  map_add' _ _ := by ext1; simp [sum_add_distrib]
  map_smul' _ _ := by ext1; simp [Finset.smul_sum]
noncomputable def gradT : Grid (TR pol) →ₗ[K] Grid (VR pol) where
  toFun x z := deriv K s z.2.1 x (z.1,z.2.2)
  map_add' _ _ := by ext1; simp only [map_add,Pi.add_apply]
  map_smul' _ _ := by ext1; simp only [map_smul,Pi.smul_apply,RingHom.id_apply]
noncomputable def divT : Grid (TR pol) →ₗ[K] Grid (WR pol) where
  toFun x z := ∑ i : Axis, deriv K s i x (z.1,Duo.sym i z.2)
  map_add' _ _ := by ext1; simp only [map_add,Pi.add_apply,sum_add_distrib]
  map_smul' _ _ := by ext1; simp only [map_smul,Pi.smul_apply,Finset.smul_sum,RingHom.id_apply]
noncomputable def gradW : Grid (WR pol) →ₗ[K] Grid (DR pol) where
  toFun x z := deriv K s z.2.1 x (z.1,z.2.2)
  map_add' _ _ := by ext1; simp only [map_add,Pi.add_apply]
  map_smul' _ _ := by ext1; simp only [map_smul,Pi.smul_apply,RingHom.id_apply]
noncomputable def divV : Grid (VR pol) →ₗ[K] Grid (DR pol) where
  toFun x z := ∑ i : Axis, deriv K s i x (z.1,z.2.1,Duo.sym i z.2.2)
  map_add' _ _ := by ext1; simp only [map_add,Pi.add_apply,sum_add_distrib]
  map_smul' _ _ := by ext1; simp only [map_smul,Pi.smul_apply,Finset.smul_sum,RingHom.id_apply]

@[simp] lemma gradT_apply (x : Grid (TR pol)) (z : VR pol) : gradT K s x z = (s z.2.1).den * x (z.1,z.2.2) := rfl
@[simp] lemma gradW_apply (x : Grid (WR pol)) (z : DR pol) : gradW K s x z = (s z.2.1).den * x (z.1,z.2.2) := rfl
@[simp] lemma divT_apply (x : Grid (TR pol)) (z : WR pol) : divT K s x z = ∑ i, (s i).den * x (z.1,Duo.sym i z.2) := rfl
@[simp] lemma divV_apply (x : Grid (VR pol)) (z : DR pol) : divV K s x z = ∑ i, (s i).den * x (z.1,z.2.1,Duo.sym i z.2.2) := rfl
@[simp] lemma traceT_apply (x : Grid (TR pol)) (z : pol × Unit) : traceT K x z = ∑ i : Axis, x (z.1,Duo.sym i i) := rfl

lemma closed (x : Grid (TR pol)) : divV K s (gradT K s x) = gradW K s (divT K s x) := by
  ext1 z; simp [mul_sum,mul_left_comm]
lemma monoT (h : (s 0).den ≠ 0) (pol : Type) : Function.Injective (gradT K s (pol:=pol)) := fun _ _ e =>
  funext fun z => mul_left_cancel₀ h (congr_fun e (show VR pol from (z.1,0,z.2)))

-- explicit parentheses in sum syntax tree for kernel checks.
def four (x : Axis → Expr) : Expr := x 0 + x 1 + (x 2 + x 3)
lemma four_den (x : Axis → Expr) : (four x).den = ∑ i : Axis, (x i).den := by
  simp [four, Fin.sum_univ_succ]; abel

def rawTrace (x : Raw (TR pol)) : Raw (pol × Unit) := fun z => four fun i => x (z.1,Duo.sym i i)
def rawDiv (x : Raw (TR pol)) : Raw (WR pol) := fun z => four fun i => s i * x (z.1,Duo.sym i z.2)
def rawT (x : Raw (TR pol)) : Raw (VR pol) := fun z => s z.2.1 * x (z.1,z.2.2)
def rawW (x : Raw (WR pol)) : Raw (DR pol) := fun z => s z.2.1 * x (z.1,z.2.2)
def rawV (x : Raw (VR pol)) : Raw (DR pol) := fun z => four fun i => s i * x (z.1,z.2.1,Duo.sym i z.2.2)
-- prefer no simp as K ambiguous
lemma luTrace (x : Raw (TR pol)) : (rawTrace x).denote = traceT K x.denote := by ext1; simp [Raw.denote,rawTrace,four_den]
lemma luDiv (x : Raw (TR pol)) : (rawDiv s x).denote = divT K s x.denote := by ext1; simp [Raw.denote,rawDiv,four_den]
lemma luGT (x : Raw (TR pol)) : (rawT s x).denote = gradT K s x.denote := by ext1; simp [Raw.denote,rawT]
lemma luGW (x : Raw (WR pol)) : (rawW s x).denote = gradW K s x.denote := by ext1; simp [Raw.denote,rawW]
lemma luV (x : Raw (VR pol)) : (rawV s x).denote = divV K s x.denote := by ext1; simp [Raw.denote,rawV,four_den]
end Derivative
end SatinStress.U1

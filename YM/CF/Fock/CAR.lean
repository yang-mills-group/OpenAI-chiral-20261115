import YM.CF.Fock.Coord
set_option linter.unusedSectionVars false

set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Finset
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n] [Fintype n]
def create : Ket n →ₗ[ℂ] FC n where
  toFun x := ∑ i, (x.ofLp i) • put i
  map_add' x y := by simp [add_smul,sum_add_distrib]
  map_smul' c x := by simp [smul_sum,mul_smul]
lemma create_def (x : Ket n) : create x=∑ i, (x.ofLp i) • put i := rfl
@[fun_prop] lemma create_cont : Continuous (create (n:=n)) := create.continuous_of_finiteDimensional
@[simp] lemma create_put (i : n) : create (basisKet i)=put i := by
  rw [create_def]; simp [ite_smul]
abbrev remove (x : Ket n) : FC n := star (create x)
lemma remove_def (x : Ket n) : remove x=∑ i, star (x.ofLp i) • takeF i := by simp [remove,create_def,takeF]
@[simp] lemma remove_take (i : n) : remove (basisKet i)=takeF i := by unfold remove; rw [create_put]
abbrev antiB (A B : FC n) := A*B+B*A
lemma antiB_comm (A B : FC n) : antiB B A=antiB A B := add_comm _ _
lemma antiB_sum {S : Type*} (s : Finset S) (A : S → FC n) (B) :
    antiB (∑ i∈s, A i) B=∑ i∈s, antiB (A i) B := by simp [antiB,sum_mul,mul_sum,sum_add_distrib]
lemma antiB_sum' {S : Type*} (s : Finset S) (A) (B : S → FC n) :
    antiB A (∑ i∈s, B i)=∑ i∈s, antiB A (B i) := by simp [antiB,sum_mul,mul_sum,sum_add_distrib]
lemma antiB_smul (c : ℂ) (A B : FC n) : antiB (c • A) B=c • antiB A B := by
  unfold antiB; rw [smul_add,Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
lemma antiB_smul' (c : ℂ) (A B : FC n) : antiB A (c • B)=c • antiB A B := by
  rw [antiB_comm,antiB_smul,antiB_comm B]
theorem car (x y : Ket n) : remove x * create y+create y*remove x=inner ℂ x y • 1 := by
  change antiB _ _=_
  rw [remove_def,create_def,antiB_sum,EuclideanSpace.inner_eq_star_dotProduct]
  simp_rw [antiB_sum',antiB_smul,antiB_smul',antiB,mixed]
  simp [apply_ite _ _,Finset.sum_smul,dotProduct,smul_smul,mul_comm]
theorem car_create (x y : Ket n) : create x*create y+create y*create x=0 := by
  change antiB _ _=0
  rw [create_def,create_def,antiB_sum]; simp_rw [antiB_sum',antiB_smul,antiB_smul',antiB,put_put]; simp
lemma create_sq (x : Ket n) : create x*create x=0 := by
  have h := car_create x x
  ext i j; exact add_self_eq_zero.mp (Matrix.ext_iff.mpr h i j)
abbrev vacuum (n : Type*) [LinearOrder n] := basisKet (∅ : Finset n)
@[simp] lemma vacuum_take (x : Ket n) : acts (remove x) (vacuum n)=0 := by
  rw [remove_def,act_sum]; simp_rw [act_smul,vacuum,take_act]; simp
lemma basis_vac (i : n) (s : Finset n) (g : i∈s) : (basisKet s).ofLp ∅=0 := by
  have h := (Finset.nonempty_iff_ne_empty.mp ⟨i,g⟩).symm; rw [basis_apply]; exact if_neg h
end YM.CF.Fock

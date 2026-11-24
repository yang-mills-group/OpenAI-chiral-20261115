import YM.CF.Operator.Spectral
import YM.CF.Operator.Blocks

/-! Coordinate ket helpers in the L2-operator conventions. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
variable {n : Type*} [Fintype n] [DecidableEq n]
lemma act_mul (A B : Op n) (x : Ket n) : acts (A*B) x=acts A (acts B x) := by rw [acts,map_mul]; rfl
lemma act_add (A B : Op n) (x : Ket n) : acts (A+B) x=acts A x+acts B x := by rw [acts,map_add]; rfl
lemma act_sub (A B : Op n) (x : Ket n) : acts (A-B) x=acts A x-acts B x := by rw [acts,map_sub]; rfl
lemma act_neg (A : Op n) (x : Ket n) : acts (-A) x= -acts A x := by rw [acts,map_neg]; rfl
lemma act_smul (c : ℂ) (A : Op n) (x : Ket n) : acts (c • A) x=c • acts A x := by rw [acts,map_smul]; rfl
lemma act_sum {S : Type*} (s : Finset S) (A : S → Op n) (x : Ket n) :
    acts (∑ i ∈ s, A i) x=∑ i ∈ s, acts (A i) x := by
  unfold acts; rw [map_sum, ContinuousLinearMap.sum_apply]
@[simp] lemma act_one (x : Ket n) : acts 1 x=x := by rw [acts,map_one]; rfl
@[simp] lemma act_zero (x : Ket n) : acts 0 x=0 := by rw [acts,map_zero]; rfl
lemma act_unit (U : UNI n) (x : Ket n) : acts (star U.val) (acts U.val x)=x := by
  rw [← act_mul,show star U.val * U.val=1 from U.property.1,act_one]
lemma act_starUnit (U : UNI n) (x : Ket n) : acts U.val (acts (star U.val) x)=x := by
  rw [← act_mul,show U.val * star U.val=1 from U.property.2,act_one]
lemma act_inner (A : Op n) (x y : Ket n) : inner ℂ (acts (star A) x) y=inner ℂ x (acts A y) := by
  unfold acts; rw [map_star,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
lemma act_unit_inner (U : UNI n) (x y : Ket n) : inner ℂ (acts U.val x) (acts U.val y) = inner ℂ x y := by
  nth_rw 1 [← star_star U.val]; rw [act_inner,act_unit]
@[simp] lemma act_unit_norm (U : UNI n) (x : Ket n) : ‖acts U.val x‖=‖x‖ := by
  have h := act_unit_inner U x x
  -- use real-part
  have : ‖acts U.val x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜:=ℂ), ← inner_self_eq_norm_sq (𝕜:=ℂ),h]
  nlinarith [norm_nonneg x,norm_nonneg (acts U.val x)]
@[fun_prop] lemma acts_cont : Continuous (acts (n:=n)) :=
  (Matrix.toEuclideanCLM (n:=n) (𝕜:=ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional

abbrev basisKet (i : n) := EuclideanSpace.single i (1:ℂ)
@[simp] lemma basis_apply (i j : n) : (basisKet i).ofLp j = if j=i then 1 else 0 := by simp [basisKet]
@[simp] lemma basis_act (A : Op n) (i j : n) : (acts A (basisKet j)).ofLp i = A i j := by rw [act_at]; simp [basisKet]
lemma basis_expand (x : Ket n) : (∑ i, (x.ofLp i) • basisKet i)=x := by
  apply PiLp.ext; intro j; simp [WithLp.ofLp_sum,Finset.sum_apply,Pi.single_apply]
lemma op_columns {A B : Op n} (h : ∀ i, acts A (basisKet i)=acts B (basisKet i)) : A=B := by
  ext i j
  rw [← basis_act A, h,basis_act]
@[simp] lemma basis_inner (x : Ket n) (i) : inner ℂ (basisKet i) x = x.ofLp i := by simp [basisKet,EuclideanSpace.inner_single_left]
lemma op_scale_column {A : Op n} (f : n → ℂ)
    (h : ∀ i, acts A (basisKet i)=f i • basisKet i) : A=Matrix.diagonal f := by
  apply op_columns; intro i
  rw [h]; apply PiLp.ext; intro j; by_cases g:i=j
  · subst j; simp
  · have he := Ne.symm g; simp [Pi.single_apply,g,he]
end YM.CF

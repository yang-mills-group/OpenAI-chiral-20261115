import YM.CF.Matter.Indices
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Star

/-! Traces for this differential, on the group used here. No result about
nonperturbative anomaly cancellation from perturbative matching. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF
open scoped Matrix.Norms.L2Operator Matrix Kronecker Topology BigOperators
attribute [local instance] opCStarAlgebra
open Finset
section
variable {n : Type*} [Fintype n] [DecidableEq n]
lemma op_deriv {f : ℝ → Op n} {a : Op n} {x} :
    HasDerivAt f a x ↔ ∀ i j, HasDerivAt (fun t => f t i j) (a i j) x := by
  simp only [hasDerivAt_iff_tendsto_slope]
  change Filter.Tendsto _ _ (@nhds (n → n → ℂ) _ a) ↔ _
  rw [tendsto_pi_nhds]; simp only [tendsto_pi_nhds]; rfl
lemma det_one_deriv {f : ℝ → Op n} {a : Op n} {x} (hv : f x=1) (h : HasDerivAt f a x) :
    HasDerivAt (fun t => (f t).det) a.trace x := by
  have hs := op_deriv.mp h
  let d (g : Equiv.Perm n) := g.sign • (∑ i : n, ((∏ j ∈ univ.erase i, f x (g j) j) • a (g i) i))
  have hg (g : Equiv.Perm n) : HasDerivAt (fun t => g.sign • (∏ i, f t (g i) i)) (d g) x := by
    have hx := HasDerivAt.fun_finsetProd (u:=Finset.univ) fun i _ => hs (g i) i
    dsimp only [d]
    -- sign either +/-
    rcases Int.units_eq_one_or g.sign with e|e
    · simpa only [e,one_smul] using hx
    rw [e]
    simp only [Units.smul_def, Units.val_neg, Units.val_one, neg_smul, one_smul]
    exact hx.neg
  simp_rw [Matrix.det_apply]
  convert! HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ => hg i) using 1
  rw [sum_eq_single (1 : Equiv.Perm n)]
  · simp +instances [Matrix.trace,d,hv]
    congr! 1
    rw [prod_eq_one (fun i _ => ?_), one_mul]; exact Matrix.one_apply_eq i
  · intro p _ hp
    have ha (i : n) : ∃ j ≠ i, p j ≠ j := by
      by_contra! hJ
      apply hp; ext j; change p j = j
      by_cases e:j=i
      · subst j; by_contra he; have hh := hJ (p i) he; exact he (p.injective hh)
      exact hJ j e
    apply Eq.trans (congrArg (p.sign • ·) (sum_eq_zero (f:=fun i => (∏ j ∈ univ.erase i, f x (p j) j) • a (p i) i) (s:=univ) (fun i _ => ?_))) (smul_zero _)
    obtain ⟨j,hj,e⟩ := ha i; rw [prod_eq_zero (Finset.mem_erase.mpr ⟨hj,Finset.mem_univ j⟩),zero_smul]
    rw [hv]; exact Matrix.one_apply_ne e
  simp

end
variable {n : Type*} [Fintype n]
lemma gen_entry [LinearOrder n] (A : Op n) (i j : ExTwo.Idx n) :
    ExTwo.gen A i j = A i.val.1 j.val.1 * (1:Op n) i.val.2 j.val.2 + (1:Op n) i.val.1 j.val.1*A i.val.2 j.val.2 -
      (A i.val.1 j.val.2*(1:Op n) i.val.2 j.val.1+(1:Op n) i.val.1 j.val.2*A i.val.2 j.val.1) := by
  rw [← ExTwo.q_read (ExTwo.gen A) i, ExTwo.gen_tensor,ExTwo.multiply_q]; simp [ExTwo.current]
  rfl

namespace SU

def sheetD (A : Op F) : Op Sheet := Join.both (ExTwo.gen A) (cc A)
def dMatter (A : Op F) : Op Slot := (1:Op (Fin 3)) ⊗ₖ sheetD A
lemma eachD {f : ℝ → Op F} {X : Op F} (hv : f 0=1) (h : HasDerivAt f X 0) :
    HasDerivAt (fun t => each (f t)) (sheetD X) 0 := by
  have he := op_deriv.mp h
  apply op_deriv.mpr; rintro (i|i) (j|j)
  · change HasDerivAt (fun t => ExTwo.wedgeOp (f t) i j) (ExTwo.gen X i j) 0
    simp_rw [ExTwo.wedge_entry]
    rw [gen_entry]
    rw [← hv]; exact ((he i.val.1 j.val.1).fun_mul (he i.val.2 j.val.2)).sub ((he i.val.1 j.val.2).fun_mul (he i.val.2 j.val.1))
  · exact hasDerivAt_const ..
  · exact hasDerivAt_const ..
  exact (he i j).star
lemma actual {f : ℝ → E} {X : Op F} (hv : f 0=1) (h : HasDerivAt (fun t => fund (f t)) X 0) :
    HasDerivAt (fun t => (matter (f t)).val) (dMatter X) 0 := by
  apply op_deriv.mpr
  rintro ⟨b,i⟩ ⟨c,j⟩
  have he := op_deriv.mp (eachD (f:=fun t=>fund (f t)) (by rw [hv,fund_one]) h) i j
  simp only [matter_matrix,triple,dMatter,Matrix.kronecker_apply]
  exact he.const_mul _
structure suLie (X : Op F) : Prop where
  skew : star X= -X
  erase : X.trace=0
lemma incoming {f : ℝ → E} {X : Op F} (hv : f 0=1) (h : HasDerivAt (fun t => fund (f t)) X 0) : suLie X := by
  have ht := h.fun_mul h.star
  have hh : (fun i => fund (f i)*star (fund (f i)))=(fun _ => 1) := funext fun i => (fund_U _).2
  rw [hh,hv,fund_one,star_one,mul_one,one_mul] at ht
  refine ⟨?_,?_⟩
  · rw [eq_neg_iff_add_eq_zero, add_comm]
    exact ht.unique (hasDerivAt_const ..)
  have he := det_one_deriv (f:=fun t => fund (f t)) (by rw [hv,fund_one]) h
  simp only [fund_det] at he
  exact he.unique (hasDerivAt_const ..)

lemma traceD (X : Op F) (k : ℕ) : (dMatter X ^ k).trace=3*((ExTwo.gen X ^ k).trace+(cc X ^ k).trace) := by
  have hx (j : ℕ) : dMatter X ^ j = (1 : Op (Fin 3)) ⊗ₖ Join.both (ExTwo.gen X ^ j) (cc X ^ j) := by
    induction j with
    | zero => simp only [pow_zero, Join.both_one,Matrix.one_kronecker_one]
    | succ j ih => rw [pow_succ,ih,dMatter,sheetD,op_kron_mul,mul_one, Join.both_mul,pow_succ,pow_succ]
  rw [hx, Matrix.trace_kronecker, Matrix.trace_one]
  norm_num [Matrix.trace, Fintype.sum_sum_type, Join.both,Sheet]

theorem local_polynomial (X : Op F) (h : suLie X) :
    (dMatter X).trace=0 ∧ (dMatter X ^ 2).trace=12*(X^2).trace ∧
      (dMatter X ^ 3).trace=0 := by
  rw [show Matrix.trace (dMatter X)=_ from congrArg Matrix.trace (pow_one (dMatter X)).symm,
      traceD,traceD,traceD,pow_one,pow_one, ExTwo.trace_gen, ExTwo.quad_gen, ExTwo.cubic_gen]
  simp only [cc, h.skew, ← Matrix.transpose_pow,Matrix.trace_transpose, Matrix.trace_neg,h.erase]
  rw [Odd.neg_pow (by decide : Odd 3), Matrix.trace_neg]
  norm_num [F,h.erase]; try ring
end SU
end YM.CF

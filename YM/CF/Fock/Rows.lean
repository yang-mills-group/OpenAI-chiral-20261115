import YM.CF.Fock.Line
set_option linter.unusedSectionVars false

/-! Coordinates and exterior degree support. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Finset
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n] [Fintype n]
lemma put_row (i : n) (x : Wave n) (t : Finset n) : (acts (put i) x).ofLp t=if i∈t then parity i t*x.ofLp (t.erase i) else 0 := by
  rw [← basis_inner,←act_inner]
  change inner ℂ (acts (takeF i) _) _=_
  rw [take_act]; by_cases h:i∈t <;> simp only [h,ite_true,ite_false]
  · rw [inner_smul_left,basis_inner]; change star _*_= _; rw [parity_star]
  simp
lemma take_row (i : n) (x : Wave n) (t : Finset n) : (acts (takeF i) x).ofLp t=if i∈t then 0 else parity i t*x.ofLp (insert i t) := by
  rw [← basis_inner,←act_inner]; unfold takeF; rw [star_star,put_act]; by_cases h:i∈t <;> simp only [h,ite_true,ite_false]
  · simp
  rw [inner_smul_left,basis_inner]; change star _*_= _; rw [parity_star]
def Degree (j : ℕ) (x : Wave n) := ∀ i : Finset n, i.card≠j → x.ofLp i=0
lemma Degree.putD {j : ℕ} {x : Wave n} (h : Degree j x) (k : n) : Degree (j+1) (acts (put k) x) := by
  intro t ht; rw [put_row]; by_cases g:k∈t
  · rw [if_pos g,h,mul_zero]; intro hc; apply ht
    nth_rw 1 [← insert_erase g]; rw [card_insert_of_notMem (by simp),hc]
  exact if_neg g
lemma Degree.scale {j : ℕ} {x : Wave n} (h : Degree j x) (c : ℂ) : Degree j (c • x) := by intro i e; simp [h i e]
lemma Degree.sumD {I : Type*} {s : Finset I} {j : ℕ} {x : I → Wave n} (h : ∀ i ∈ s, Degree j (x i)) : Degree j (∑ i∈s, x i) := by
  intro k g; rw [WithLp.ofLp_sum,Finset.sum_apply,sum_eq_zero fun i l => h i l k g]
lemma Degree.createD {j : ℕ} {x : Wave n} (h : Degree j x) (v : Ket n) : Degree (j+1) (acts (create v) x) := by
  rw [create_def,act_sum]; apply Degree.sumD; intro i _; rw [act_smul]; exact (h.putD _).scale _
lemma basis_degree (i : Finset n) : Degree i.card (basisKet i) := by intro j h; rw [basis_apply]; exact if_neg (fun e => h (congrArg _ e))
lemma Degree.too_big {j : ℕ} {x : Wave n} (h : Degree j x) (g : Fintype.card n < j) : x=0 := by
  apply PiLp.ext; intro i; rw [h i ((lt_of_le_of_lt (card_le_univ i) g).ne)]; rfl
end YM.CF.Fock

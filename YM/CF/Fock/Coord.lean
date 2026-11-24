import YM.CF.Fock.Ket

/-! Unconstrained finite CAR Fock representation. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Finset
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n]

abbrev FC (n : Type*) := Op (Finset n)
abbrev Wave (n : Type*) := Ket (Finset n)
/-- Order sign, counts strictly smaller occupied coordinates. -/
def parity (i : n) (s : Finset n) : ℂ := (-1) ^ (s.filter (· < i)).card
lemma parity_lo (s : Finset n) (i j : n) (h : j < i) (g : j∉s) :
    parity i (insert j s)= -parity i s := by simp [parity,filter_insert,h,g,pow_succ]
lemma parity_hi (s : Finset n) (i j : n) (h : i≤j) :
    parity i (insert j s)=parity i s := by simp [parity,filter_insert, not_lt.mpr h]
lemma parity_erase (s : Finset n) (i : n) (h : i∈s) : parity i (s.erase i)=parity i s := by nth_rw 2 [← insert_erase h]; rw [parity_hi _ _ _ le_rfl]
@[simp] lemma parity_star (i : n) (s : Finset n) : star (parity i s)=parity i s := by simp [parity]
@[simp] lemma parity_sq (i : n) (s : Finset n) : parity i s*parity i s=1 := by simp [parity,← mul_pow]

/-- Create, by specifying column. -/
def put (i : n) : FC n := Matrix.of fun p q =>
    if i∈q then 0 else if p=insert i q then parity i q else 0
lemma put_entry (i : n) (p q) : put i p q = if i∈q then 0 else if p=insert i q then parity i q else 0 := rfl
abbrev takeF (i : n) := star (put i)
lemma take_entry (i : n) (p q) : takeF i p q = if i∈q then if p=q.erase i then parity i q else 0 else 0 := by
  change star (put i q p)=_
  rw [put_entry]
  by_cases he:i∈p
  · simp only [he,ite_true,star_zero]; have hp : p≠q.erase i := by intro h; rw [h] at he; simp at he
    simp [hp]
  rw [if_neg he]; by_cases h : q=insert i p
  · subst q; simp [he,parity_hi _ _ _ le_rfl]
  rw [if_neg h,star_zero]; by_cases g:i∈q
  · have hne : p≠q.erase i := by intro hh; subst p; exact h (insert_erase g).symm
    simp [g,hne]
  simp [g]

variable [Fintype n]
lemma put_act (i : n) (s : Finset n) : acts (put i) (basisKet s) =
    if i∈s then 0 else parity i s • basisKet (insert i s) := by
  apply PiLp.ext; intro t; change (acts _ _).ofLp t=_
  rw [basis_act,put_entry]; by_cases h:i∈s
  · simp [h]
  rw [if_neg h,if_neg h]; by_cases g:t=insert i s <;> simp [g]
lemma take_act (i : n) (s : Finset n) : acts (takeF i) (basisKet s) =
    if i∈s then parity i s • basisKet (s.erase i) else 0 := by
  apply PiLp.ext; intro t; change (acts _ _).ofLp t=_
  rw [basis_act,take_entry]; by_cases h:i∈s
  · rw [if_pos h,if_pos h]; by_cases g:t=s.erase i <;> simp [g]
  simp [h]
lemma put_sq (i : n) : put i*put i=0 := by
  apply op_columns; intro s
  rw [act_mul,put_act]; by_cases g:i∈s <;> simp [g,put_act]
lemma put_put (i j : n) : put i*put j+put j*put i=0 := by
  suffices h : ∀ i j:n, i<j → put i*put j+put j*put i=0 by
    rcases lt_trichotomy i j with hlt|he|hgt; exact h _ _ hlt; rw [he,put_sq,zero_add]; rw [add_comm,h _ _ hgt]
  intro i j hij
  have hne := ne_of_lt hij; have hnj := hne.symm
  apply op_columns; intro s
  rw [act_add,act_mul,act_mul,put_act,put_act]; by_cases g:i∈s <;> by_cases e:j∈s
  · simp [g,e]
  · simp [g,e,put_act]
  · simp [g,e,put_act]
  simp [g,e,put_act,hne,hnj,parity_lo s j i hij g,parity_hi s i j hij.le,smul_smul,mul_comm,
    insert_comm i j]
lemma occ_act (i : n) (s : Finset n) : acts (put i*takeF i) (basisKet s)= if i∈s then basisKet s else 0 := by
  rw [act_mul,take_act]; by_cases g:i∈s <;> simp [g,put_act]
  simp [parity_erase _ _ g, smul_smul]
lemma vacant_act (i : n) (s : Finset n) : acts (takeF i*put i) (basisKet s)= if i∈s then 0 else basisKet s := by
  rw [act_mul,put_act]; by_cases g:i∈s <;> simp [g,take_act]
  simp [parity_hi _ _ _ le_rfl,smul_smul]
lemma mixed_off (i j : n) (h : i<j) : takeF i * put j+put j*takeF i=0 := by
  apply op_columns; intro s
  rw [act_add,act_mul,act_mul,put_act,take_act,act_zero]; by_cases g:i∈s <;> by_cases e:j∈s
  · simp [g,e,put_act,(ne_of_gt h)]
  · let t := s.erase i
    have ht : i∉t := by simp [t]
    have hz : j∉t := fun l => e (mem_of_mem_erase l)
    -- replace s with inserted to track signs
    rw [← show insert i t=s from insert_erase g]
    have hx := ne_of_gt h
    simp only [mem_insert,hx,hz,or_self, mem_erase, or_true, true_or,
      ite_true,ite_false, map_smul, take_act, put_act]
    rw [insert_comm j i]; simp [ht,hx, hx.symm, parity_hi _ i _ le_rfl,parity_hi t i j h.le,
      parity_lo t j i h ht, smul_smul,mul_comm]
  · simp [g,e]
  · simp [g,e,take_act,ne_of_lt h]
lemma mixed (i j : n) : takeF i*put j+put j*takeF i = (if i=j then 1 else 0) := by
  rcases lt_trichotomy i j with h|h|h
  · simp [mixed_off i j h,ne_of_lt h]
  · subst j; rw [if_pos rfl]; apply op_columns; intro s
    rw [act_add,vacant_act,occ_act]; by_cases h:i∈s <;> simp [h]
  rw [if_neg (ne_of_gt h)]
  have he := congrArg star (mixed_off j i h)
  simpa [takeF] using he
lemma take_take (i j : n) : takeF i*takeF j+takeF j*takeF i=0 := by
  have he := congrArg star (put_put j i); simpa [takeF] using he
end YM.CF.Fock

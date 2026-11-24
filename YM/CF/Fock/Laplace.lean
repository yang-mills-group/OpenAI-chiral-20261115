import YM.CF.Fock.Volume

/-! Expansion by a row or a coordinate pair. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Finset
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n] [Fintype n]
lemma quantum_at (A : Op n) (s t) : quant A s t=(wedge A t).ofLp s := rfl
lemma spread (A : Op n) (s t : Finset n) (i : n) (h : i ∈ t) : quant A s t = parity i t * ∑ j∈s, A j i * (parity j s*quant A (s.erase j) (t.erase i)) := by
  nth_rw 1 [quantum_at,←insert_erase h]; -- changes t
  rw [wedge_any _ _ _ (by simp),WithLp.ofLp_smul, Pi.smul_apply,smul_eq_mul,parity_erase _ _ h,create_def,act_sum,WithLp.ofLp_sum, Finset.sum_apply]
  congr 1
  rw [←sum_subset (subset_univ s)]; swap
  · intro j _ g; rw [act_smul,WithLp.ofLp_smul,Pi.smul_apply,put_row,if_neg g,smul_zero]
  apply sum_congr rfl; intro j g; rw [act_smul,WithLp.ofLp_smul,Pi.smul_apply,basis_act,put_row,if_pos g]; rfl
lemma solo_col (A : Op n) (s t : Finset n) (i j : n) (h : i∈t) (g : j∈s) (e : ∀ k ∈ s, k ≠ j → A k i=0) :
    quant A s t= parity i t * (A j i * (parity j s*quant A (s.erase j) (t.erase i))) := by
  rw [spread _ _ _ _ h,sum_eq_single_of_mem _ g]; intro b hb k; rw [e b hb k,zero_mul]
lemma solo_row (A : Op n) (s t : Finset n) (i j : n) (h : i∈s) (g : j∈t) (e : ∀ k ∈ t, k ≠ j → A i k=0) :
    quant A s t= parity i s * (A i j * (parity j t*quant A (s.erase i) (t.erase j))) := by
  have he : ∀ a b, quant (star A) b a=star (quant A a b) := by intro a b; rw [quant_star]; rfl
  apply star_injective; rw [←he,solo_col _ _ _ _ _ h g (fun k hk hl=>by simp [e k hk hl]),he]; simp [star_mul,mul_comm]
lemma exchangeParity {s : Finset n} {a b : n} (h : a∈s) (g : b∈s) (e : a≠b) :
    parity a (s.erase b)*parity b (s.erase a)= -(parity a s*parity b s) := by
  have he (a b) (g : b∈s) (k : a < b) : parity a (s.erase b)=parity a s := by nth_rw 2 [←insert_erase g]; rw [parity_hi _ _ _ k.le]
  have hg (a b) (g : b∈s) (k : b < a) : parity a (s.erase b)= -parity a s := by nth_rw 2 [←insert_erase g]; rw [parity_lo _ _ _ k (by simp),neg_neg]
  rcases lt_or_gt_of_ne e with k|k
  · rw [he _ _ g k,hg _ _ h k]; simp
  rw [hg _ _ g k,he _ _ h k]; simp
/-- pfaffian minor with order sign fixed by pair exponential. -/
def pf (A : Op n) (s : Finset n) := (pairWave A).ofLp s
lemma pf_spread (A : Op n) (g : Aᵀ= -A) (s : Finset n) (i : n) (h : i∈s) :
    parity i s*pf A s= ∑ j∈s.erase i, A i j*(parity j (s.erase i)*pf A ((s.erase i).erase j)) := by
  let w := pairWave A; let t := s.erase i
  have he : (acts (takeF i) w).ofLp t=(acts A (insertRows w t)).ofLp i := pull_rows g t i
  rw [take_row, if_neg (show i∉t from notMem_erase i s),show insert i t=s from insert_erase h,act_at,show parity i t=parity i s from parity_erase s i h] at he
  change parity i s * w.ofLp s=∑ j∈t, _; rw [he]
  change ∑ j, A i j * (acts (put j) w).ofLp t=∑ j∈t, A i j * (parity j t * pf A (t.erase j)); rw [←sum_subset t.subset_univ]
  · apply sum_congr rfl; intro j hj; rw [put_row,if_pos hj]; rfl
  intro i _ hi; rw [put_row,if_neg hi,mul_zero]
lemma skew_swap (A : Op n) (g : Aᵀ= -A) (i j) : A j i= -A i j := Matrix.ext_iff.mpr g i j
lemma skew_diag (A : Op n) (g : Aᵀ= -A) (i : n) : A i i=0 := add_self_eq_zero.mp (add_eq_zero_iff_eq_neg.mpr (skew_swap A g i i))
lemma matched (A : Op n) (g : Aᵀ= -A) (s : Finset n) (a b : n) (h : a∈s) (k : b∈s) (e : b≠a)
    (q : ∀ i∈s, i ≠ b → A a i=0) : quant A s s=A a b * A a b * quant A ((s.erase a).erase b) ((s.erase a).erase b) := by
  have ha : ∀ i∈s, i≠ b → A i a=0 := by intro i hi hx; rw [skew_swap A g,q _ hi hx,neg_zero]
  rw [solo_col A s s _ _ h k ha,solo_row A (s.erase b) (s.erase a) a b (mem_erase.mpr ⟨e.symm,h⟩) (mem_erase.mpr ⟨e,k⟩) (fun i hi=>q i (mem_of_mem_erase hi)),show (s.erase b).erase a=(s.erase a).erase b by ext; simp; tauto, skew_swap A g a b]
  let x := parity a s*parity b s; have he := exchangeParity h k e.symm
  have hk : x * (parity a (s.erase b)*parity b (s.erase a)) = -1 := by unfold x; rw [he,mul_neg,mul_mul_mul_comm,parity_sq,parity_sq,mul_one]
  calc _ = -(x*(parity a (s.erase b)*parity b (s.erase a))) * (A a b * A a b * quant A ((s.erase a).erase b) ((s.erase a).erase b)) := by unfold x; ring
       _ = _ := by rw [hk,neg_neg,one_mul]
lemma match_pf (A : Op n) (g : Aᵀ= -A) (s : Finset n) (a b : n) (h : a∈s) (k : b∈s) (e : b≠a)
    (q : ∀ i∈s, i ≠ b → A a i=0) : pf A s^2=A a b * A a b * pf A ((s.erase a).erase b)^2 := by
  have he := pf_spread A g s a h; rw [sum_eq_single_of_mem _ (mem_erase.mpr ⟨e,k⟩) (fun i hi hx=>by rw [q i (mem_of_mem_erase hi) hx,zero_mul])] at he
  have hk := congrArg (· ^ 2) he
  simp only [mul_pow] at hk; simpa only [pow_two,parity_sq,one_mul] using hk
end YM.CF.Fock

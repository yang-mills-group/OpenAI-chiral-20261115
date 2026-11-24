import CellQ.Ray
set_option autoImplicit false
set_option linter.flexible false
noncomputable section
namespace YM.CF.Drift.Grain
open Function Finset Mew
open scoped BigOperators Topology
variable {I E:Type}[Fintype I][LinearOrder I][AddCommGroup E][Module ℂ E]
local notation "nT" => (Fintype.card (PairKey I)+1)
local notation "K"=> Key (PairKey I)
attribute [-instance] instDecidableEqLex
variable {cost:E→ℝ}{α:Type}[DecidableEq α] (S:Finset α)(w:α→ℝ)(D:α→Finset I)(F:α→Mew.Key (PairKey I)→E)
lemma first_bank (hc:rateCost cost) (hf:∀ i∈S,Grain (D i) (F i))(z:K)(hp:∀ i, ‖z i‖≤1)(ht:1<nT){M:ℝ}(p:∀ i:PairKey I,∑ j∈ S,cost (F j (pulse (yard i) (altQ i) 1))≤ M) : ∑ j∈S,cost (rainbow (F j) z 1)≤Fintype.card (PairKey I)*M :=by
 have h(j:α)(hj:j∈S):cost (rainbow (F j) z 1)≤ ∑ i:PairKey I,cost (F j (pulse (yard i) (altQ i) 1)):=by
    rw [circle_first (hf _ ‹_›) z ht]; apply (hc.sumK ..).trans (sum_le_sum _); intro i _; rw [hc.scaleK]; exact mul_le_of_le_one_left (hc.low _) (hp _)
 apply (sum_le_sum h).trans; rw [sum_comm]; exact (sum_le_sum (fun i _=> p i)).trans_eq (show (∑ _i:PairKey I,M)=(Fintype.card (PairKey I):ℝ)*M by rw [sum_const,card_univ,nsmul_eq_mul])
lemma crest_all (hc:rateCost cost)(hf:∀ i∈S,Grain (D i) (F i))(z:K)(hp:∀ i, ‖z i‖≤1)(hw:∀ i∈S,0 ≤ w i){M M':ℝ}(p:∀ i:PairKey I,∑ j∈S,cost (F j (pulse (yard i) (altQ i) 1))≤ M)(h:∀ t:ℂ,‖t‖≤1→∑ i∈S,w i*cost (F i (t • z))≤ M')(l:ℝ)(τ:ℂ)(u:0≤l)(hA:∀ i∈Ico 2 nT,∀ j∈ S,i≤ (D j).card→1 ≤ l^i*w j):
 ∑ i∈ S,cost (F i (τ • z)) ≤ Fintype.card (PairKey I)*(‖τ‖*M) + M'*∑ i∈ Ico 2 nT,(‖τ‖*l)^i :=by
 by_cases he:1<nT
 · have h₀(i:α)(hi:i∈S): cost (F i (τ• z)) ≤ ∑ j∈ Ico 1 nT, ‖τ‖^j*cost (rainbow (F i) z j):=by rw [shawl (hf i ‹_›)]; refine (hc.sumK ..).trans_eq (sum_congr rfl (fun i _=>by rw [hc.scaleK,norm_pow]))
   refine (sum_le_sum h₀).trans ?_; rw [sum_comm,←Finset.sum_erase_add _ _ (mem_Ico.mpr ⟨le_rfl,he⟩)] -- lemma check. use insert_Ico_add_one_left_eq_Ico
   let N:=nT
   have hS(k:ℕ)(t:k∈Ico 2 N): ∑ i∈ S,‖τ‖^k*cost (rainbow (F i) z k)≤ M'*((‖τ‖*l)^k):=by
      have h0:= paid_order S w D F hc hw hf z h k (mem_Ico.mp t).2 (fun _=>1) (l^k) (pow_nonneg u _) (hA k t)
      simp only [one_mul] at h0; rw [←mul_sum]; exact (mul_le_mul_of_nonneg_left h0 (pow_nonneg (norm_nonneg _) _)).trans_eq (by rw [mul_pow]; ring)
   have hE: (∑ i∈ S,‖τ‖^1*cost (rainbow (F i) z 1))≤ Fintype.card (PairKey I)*(‖τ‖*M):=by rw [pow_one,←mul_sum]; exact (mul_le_mul_of_nonneg_left (first_bank S D F hc hf z hp he p) (norm_nonneg _)).trans_eq (by ring)
   rw [add_comm,mul_sum] -- add_comm maybe first
   -- combine sets
   rw [show (Ico 1 (nT:ℕ)).erase 1= Ico 2 N from (by ext i; unfold N; simp; omega)]
   exact add_le_add hE (sum_le_sum (fun i hi=> hS i hi))
 have h':nT=1:=by omega
 have hz(i:α)(hi:i∈S):F i (τ•z)=0:=by rw [shawl (hf i ‹_›),h']; simp
 rw [sum_eq_zero (fun i hi=>by rw [hz i hi,hc.zeroK]),h',Ico_eq_empty_of_le (by norm_num),sum_empty,mul_zero,add_zero]
 rw [show Fintype.card (PairKey I)=0 from (by omega),Nat.cast_zero,zero_mul]
end YM.CF.Drift.Grain

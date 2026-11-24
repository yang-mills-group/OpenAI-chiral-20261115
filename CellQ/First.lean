import CellQ.Bel
set_option autoImplicit false
set_option linter.flexible false
noncomputable section
namespace YM.CF.Drift
namespace Grain
open Function Finset Mew
open scoped BigOperators Topology
variable {I E:Type}[Fintype I][LinearOrder I][AddCommGroup E][Module ℂ E]
local notation "nT" => (Fintype.card (PairKey I)+1)
local notation "K"=> Key (PairKey I)
attribute [-instance] instDecidableEqLex
lemma circle_first {D:Finset I}{f:K→E}(e:Grain D f)(z:K)(hL:1<nT): rainbow f z 1= ∑ i:PairKey I,z i • f (pulse (yard i) (altQ i) 1):=by
 induction e with
 | zero=> simp [rainbow]
 | add _ _ h v=>simp_rw [rainbow_plus,smul_add,sum_add_distrib,h,v]
 | chip t F v p h u=>
   let g(w:K):=(∏ j∈t,Drift.entry (F j) (yard j) w) • v
   rw [rainbow_chip _ _ _ _ _ hL]
   change (if t.card=1 then g z else 0) = ∑ i:PairKey I,z i • g (pulse (yard i) (altQ i) 1)
   by_cases hp:t.card=1
   · obtain ⟨i,r⟩:=card_eq_one.mp hp; subst t
     have he(w:K):g w= Drift.entry (F i) (yard i) w • v:=by simp [g]
     simp_rw [if_pos hp,he,smul_smul]
     rw [←sum_smul]; apply congrArg (· • v)
     unfold Drift.entry; simp_rw [mul_add,sum_add_distrib,pulse,pick,altQ,yard]
     have hU (b:Bool)(j:PairKey I):update (0:K) (j.1,j.2) 1 (pick i.1 b)=(if pick i.1 b=j then 1 else 0):=by rw [Prod.mk.eta]; exact update_apply ..
     simp_rw [show ∀ b:Bool,∀ j:PairKey I,update (0:K) (j.1,j.2) 1 (i.1,b)=_ from hU,mul_ite,mul_zero,mul_one]
     rw [sum_ite_eq,sum_ite_eq]; simp only [mem_univ,if_true]; ring
   rw [if_neg hp]; symm; apply sum_eq_zero; intro i _; have he:∃ j∈t,yard j ≠ yard i:=by
      by_contra! u
      obtain ⟨j,hj⟩:=p; have hT:t={j}:=eq_singleton_iff_unique_mem.mpr ⟨hj,fun k hk=>h hk hj ((u k hk).trans (u j hj).symm)⟩; exact hp (hT ▸ card_singleton ..)
   obtain ⟨j,hj,k⟩:=he; unfold g; rw [prod_eq_zero hj (entry_off _ _ _ k ..),zero_smul,smul_zero]
end Grain
end YM.CF.Drift

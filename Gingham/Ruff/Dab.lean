import Gingham.Ruff.Throb

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Finset Fock Scree Pastry
open scoped Topology BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n] [Fintype n]


/-! Single substitution response and exact letter cost. -/

def tic (i j:n) : Op n := fun k l => if k=i then (if l=j then 1 else 0) else 0

lemma tic_letter (i j r:n) :
    shock (dg (tic i j)) (put r) = if r=j then put i else 0 := by
 rw [pulse_let, sum_eq_single i]; simp [tic,ite_smul]
 · intro k _ y
   simp [tic,y]
 simp

lemma tic_away (i j:n) (s:Finset n) (h:j∉s) :
    shock (dg (tic i j)) (poke s)=0 := by
  induction s using Finset.induction_on with
  | empty =>
      rw [show poke ∅=(1:FC n) from Poly.tag_void _,shock_one]
  | insert k s l ih =>
      unfold poke
      rw [Poly.tag_any _ s k l, map_smul,
          shock_times, show (cane n).term k=put k from rfl,tic_letter,
          if_neg (show k≠j from by intro e; exact h (e ▸ mem_insert_self _ _)),
          show (cane n).tag s=poke s from rfl,
          ih (fun p=>h (mem_insert_of_mem p)),zero_mul,mul_zero,add_zero,smul_zero]


lemma tic_hit (i j:n) (s:Finset n) (h:j∈s) :
    shock (dg (tic i j)) (poke s) =
      parity j (s.erase j) • (poke {i} * poke (s.erase j)) := by
  have e : poke s = parity j (s.erase j) • (put j * poke (s.erase j)) := by
    nth_rw 1 [←insert_erase h]
    exact Poly.tag_any (cane n) _ _ (notMem_erase _ _)
  rw [e,map_smul,shock_times,tic_letter,if_pos rfl,tic_away i j (s.erase j)
    (notMem_erase _ _),mul_zero,add_zero,show poke {i}=put i from Poly.tag_once (cane n) i]

lemma tic_tagTier {H:ℝ} (z:0≤H) (i j:n) (s:Finset n) :
    tier H (shock (dg (tic i j)) (poke s)) ≤ H^s.card := by
  by_cases h:j∈s
  · rw [tic_hit _ _ _ h,whiteℂ,show ‖parity j (s.erase j)‖=1 from by simp [parity],one_mul]
    apply (white_mul H z ..).trans
    rw [←pow_add,card_singleton,
      show 1+(s.erase j).card=s.card from by rw [add_comm]; exact card_erase_add_one h]
  rw [tic_away _ _ _ h,chaff]
  positivity

lemma jolt_ticTier {H:ℝ} (z:0≤H) (i j:n) (q:Dough n) :
    tier H (jolt (tic i j) q).val ≤ tier H q.val := by
  change tier _ (shock _ q.val)≤_
  nth_rw 1 [(fineShape q).allP]
  rw [map_sum]
  apply (tier_sum z ..).trans
  apply sum_le_sum
  intro s _


  rw [map_smul,whiteℂ,mul_comm]
  exact mul_le_mul_of_nonneg_right (tic_tagTier z i j s) (norm_nonneg _)

lemma jolt_tic_support {s : Finset n} {q:Dough n} (w: q∈stretch s)
    (i j:n) : jolt (tic i j) q ∈ stretch (insert i s) := by
  apply shock_flour (subset_insert i s) _ _ w
  intro k _ l p
  simp [tic,show l≠i by intro e; exact p (mem_insert.mpr (Or.inl e))]
lemma jolt_tic_out {s : Finset n} {q:Dough n} (w: q∈stretch s)
    (i j : n) (h:j∉s) : jolt (tic i j) q=0 := by
  apply Subtype.ext
  change shock (dg _) q.val = 0
  rw [(show Flour s q.val from w).pin,map_sum]
  apply sum_eq_zero
  intro r l
  have m:=mt (show j∈r → j∈s from fun u=>mem_powerset.mp (mem_filter.mp l).1 u) h
  rw [map_smul,tic_away _ _ _ m,smul_zero]


lemma dg_tic (i j:n) : dg (tic i j)= put i*takeF j := by
  unfold dg dyad
  rw [sum_eq_single i,sum_eq_single j]
  · simp [tic]
  · intro k _ hk
    simp [tic,hk]
  · simp
  · intro k _ hk
    simp [tic,hk]
  simp
lemma jolt_tuples (E : Op n) (x : Dough n) :
    jolt E x = ∑ i, ∑ j, hollow (E i j)*jolt (tic i j) x := by
  apply Subtype.ext
  change dg E*x.val - x.val*dg E=(Dough n).val _
  unfold dg dyad
  simp only [sum_mul,mul_sum,map_sum,←sum_sub_distrib]
  refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_ 
  change _= (_ • (1:FC n)) * (dg (tic i j)*x.val-x.val*dg (tic i j))
  rw [dg_tic,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc,one_mul,smul_sub]


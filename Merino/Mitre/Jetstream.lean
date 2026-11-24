import Merino.Shuttle
import YM.CF.Continuum.Salary
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 2000
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 620000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Merino.Mitre
open Fock Finset Lattice Lat Spire Scroll Cube Branch Skye Tenant RG
open scoped BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Buffered
variable {N:Side}


open Tulip Window Dial StressExchange Swell
local notation "D"=>Single N
lemma earring(W:Op D):‖preJ (tickA N) W‖≤entryBudget W+entryBudget W:=by
 let A:=tickA N
 have t:=Cascade.plus_P N
 refine (norm_add_le _ _).trans <| add_le_add ?_ (extensiveDG' A (1-A) W (t.norm_le _) (t.one_sub.norm_le _))
 rewrite [norm_smul,norm_one,mul_one, touchP]
 -- norm Trace ≤ sum 
 refine (norm_sum_le univ (fun i:D=>(cutM (Tset N) * W) i i)).trans ?_
 apply sum_le_sum;intro i _
 apply le_trans _ (single_le_sum (f:=fun j=>‖W i j‖) (fun _ _=>norm_nonneg _) (mem_univ i))
 rw [cutM,Matrix.diagonal_mul];split <;>simp


variable {y:Spool N} {a b d:ℝ} {K:Scree.Loom N}{p:BudgetPoint}
   (t:y.Hem K p a b d)
include t
-- uniform price (separate from denZ prices)
def rateOk(b:ℝ):= b+ (Fintype.card Axis)*(4*(Tenant.quota^2*b))
lemma shiftNorm (x:Site N)(i:Axis)(V:Pane N):
 ‖y.jShift K p i x V‖≤2*(Tenant.quota^2*b):=by
 have z := mask_sum t.skylight t.sign (trunk_go _ x (t.spurt i)) V
 rw [two_mul]; exact le_trans (earring _) <| add_le_add z z
lemma initial (c:ℂ)(V:Pane N):
 ‖y.opening K p c V‖≤‖c‖* rateOk b:=by
 unfold Spool.opening Spool.patchwork rateOk
 rw [Pi.smul_apply,norm_smul,Pi.add_apply]
 apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
 refine (norm_add_le ..).trans (add_le_add ?_ ?_)
 · rw [Spool.scalar,sheen,norm_smul,norm_one,mul_one];exact mask_trace t.skylight t.sign t.sip _
 unfold Spool.jumps
 rw [Finset.sum_apply,←nsmul_eq_mul,←card_univ,←Finset.sum_const]
 refine (norm_sum_le ..).trans (sum_le_sum ?_)
 intro i _
 rw [Pi.sub_apply]
 exact (norm_sub_le ..).trans ((add_le_add (shiftNorm t _ _ _) (shiftNorm t _ _ _)).trans_eq (by ring))

end YM.CF.Merino.Mitre

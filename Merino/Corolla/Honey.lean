import Merino.Corolla.Change
import YM.SU5.Exchange.Force.Cloud
import YM.CF.Vow.Move


set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Merino.Corolla
open Finset Lattice RG Scree Skye Vow
open scoped Topology Classical Matrix Matrix.Norms.L2Operator
open Cadre Sour Push.AbsoluteSums.Trees Vow.TreasuryFog
open Stax Mew Rive

variable {n:Side} (P:BudgetPoint)
local notation "t"=>chi_f P.order
def honey(d:Force n→ℝ)(X:Aura n)(D:Finset (Seat n)):= ∑ j ∈ motV X D, t*d j

lemma candor(d:Force n→ℝ)(u:ℝ)(y:Seat n):
    nook ((roofL (honey P d) 1)*tact u P.B) y
     = t*∑ j:Force n, giftK P u j y*d j:=by
 have cZ(Z:Finset (Aura n)): (∑ X ∈ Z, (roofL (honey P d) 1 X)*tact u P.B X)= t*∑ j, if lordD j∈Z then currency P.B u (lordD j).val*d j else 0:=by
   simp only [roofL,duty,ite_self,one_mul,honey,motV,sum_filter,sum_mul]
   conv_lhs => enter [2,X]; rw [Finset.sum_comm]
   rw [sum_comm,mul_sum]
   refine sum_congr rfl fun j _=> ?_
   by_cases w:lordD j∈Z
   · rw [sum_eq_single_of_mem (lordD j) w (fun X _ h=> by simp [Ne.symm h]), if_pos w]
     simp only [true_and]
     rw [sum_eq_single_of_mem (extraD j) (mem_powerset.mpr j.property.2) (fun i _ h=> by simp [Ne.symm h])]
     simp only [if_true,tact,currency,widthK]
     ring
   rw [if_neg w,mul_zero]
   exact sum_eq_zero fun X hX=> by simp [show lordD j ≠ X from fun h=>w (h.symm ▸ hX)]
 rw [nook]; simp only [Pi.mul_apply]
 rw [cZ]
 congr 1
 refine sum_congr rfl fun j _=> ?_
 simp [spark,lordD,giftK,ite_mul]


variable (F:ForceBudget n){Θ h v g:ℝ}{N:ℕ}
theorem repast (p:lapel P.B ≤ Θ)(hb:0≤h) (k:chi_f P.order*v<g)
    (H₁:FlagWidth P F N) (H₂: SanB F (giftK P Θ) P h (fun _=>v)):
  ∃ r:Aura n→Finset (Seat n)→ℝ, (∀ X D, D⊆X.val→Fray P h N X D (settleK F X D) (r X D))∧
    (∀ i, nook ((roofL r 1)*tact (lapel P.B) P.B) i < g):=by
 obtain ⟨d,H,S⟩:=H₂.bit
 let r:=honey P d
 have w(X:Aura n)(D:Finset (Seat n)):Fray P h N X D (settleK F X D) (r X D):=by
     exact Fray.sumP _ _ _ (fun i a=>by
       obtain ⟨z,u⟩:=(mem_filter.mp a).2; rw [←z,←u]
       exact ⟨(rimP (H i) hb).2,H₁ i⟩)
 refine ⟨r,fun X D _=>w X D,fun i=> lt_of_le_of_lt ?_ k⟩
 suffices a: nook _ i ≤ nook ((roofL r 1)*tact Θ P.B) i from
   a.trans ((candor P d Θ i).le.trans (mul_le_mul_of_nonneg_left (S i) (spicy_f _)))
 exact sum_le_sum fun X _=> mul_le_mul_of_nonneg_left (tact_para p X) (sum_nonneg fun D _=>by
   rw [duty,ite_self]; exact mul_nonneg zero_le_one ((w X D).merit.wage hb))

end YM.CF.Merino.Corolla

import Zephyr.Voucher
import Zephyr.Incidence

/-! One payment for both rates; flags and deletion not changed
when switching currencies. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Zephyr
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray

open Beau Ione
variable {n:Side}{P:BudgetPoint}{h x y:ℝ}{K L:ℕ}{X Y:RegBudget n}
variable {U:Sweep n→Prop} -- no need, head_L low Utrue?


abbrev footing(i:Scree.Hub n):=i.val.2
abbrev rootAt(i:Scree.Hub n):=i.val.1
/-- Full PressB at its *original* qualifications. -/
structure DualBill (P:BudgetPoint)(h:ℝ)(X:RegBudget n)(v:Scree.Hub n→ℝ)(x y:ℝ):Prop where
  reg i: PressB P i (X i) h (v i)
  pos i: 0≤v i
  low: Tab rootAt footing v P.B P.supportExponent x
  raised: Tab rootAt footing v P.B (P.supportExponent+1) y
open Trees
variable {E:RegBudget n}
lemma twicePay (hl:IncX Utrue E P h x) (hu:Voucher P h K y E) (hp:0≤h):
    ∃v, DualBill P h (head_L E) v x (Real.exp K*x+y):=by
 obtain ⟨Y,u,r⟩:=hu
 obtain ⟨v,f,u'⟩:=(Beau.price_Q P E hl).1.weight
 obtain ⟨w,g,t⟩:=(Beau.price_Q (plusP P) Y u).1.weight
 have t0 : Tab rootAt footing v P.B P.supportExponent x := fun i=>by rw [sum_filter]; exact u' i
 have t1 : Tab rootAt footing w P.B (P.supportExponent+1) y := fun i=>by rw [sum_filter]; exact t i
 let z(i:Scree.Hub n):= if K<coverNumber P.B (footing i) then min (w i) (v i) else v i
 have p(i:Scree.Hub n):PressB P i ((head_L E) i) h (z i):=by
   unfold z
   split
   next hi =>
     rcases min_choice (w i) (v i) with a|a

     · rw [a,r i hi]; exact (readsplus P).symm.press (g i)
     rw [a]; exact f i
   exact f i
 have zlow i:z i≤v i:= by unfold z;split;exact min_le_right ..;exact le_rfl
 refine ⟨z,p,fun i=>Beau.grit_p P (p i) hp,fun q=> (sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (zlow i) (Real.exp_pos _).le).trans (t0 q),?_⟩
 intro q
 refine le_trans ?_ (add_le_add (mul_le_mul_of_nonneg_left (t0 q) (Real.exp_pos (K:ℝ)).le) (t1 q))
 rw [mul_sum,←sum_add_distrib]
 apply sum_le_sum; intro i _
 have vf:0≤v i := grit_p P (f i) hp
 have wg:0≤w i := grit_p _ (g i) hp
 by_cases e: K<coverNumber P.B (footing i)
 · refine le_add_of_nonneg_of_le (mul_nonneg (Real.exp_pos _).le
       (mul_nonneg (Real.exp_pos _).le vf)) (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
   rw [show z i= _ from if_pos e]
   exact min_le_left ..
 refine le_add_of_le_of_nonneg ?_ (mul_nonneg (Real.exp_pos _).le wg)
 unfold due Trees.currency; rw [←mul_assoc,←Real.exp_add]
 have w': (coverNumber P.B (footing i):ℝ) ≤ K := by exact_mod_cast le_of_not_gt e
 have t:=grit_p P (p i) hp
 exact mul_le_mul (Real.exp_le_exp.mpr (by linarith only [w'])) (zlow i) t (Real.exp_pos _).le
#print axioms twicePay
end YM.CF.Zephyr

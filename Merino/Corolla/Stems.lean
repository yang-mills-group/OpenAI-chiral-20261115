import Merino.Corolla.Train
import YM.SU5.Exchange.Seed.Pip

set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 360000
noncomputable section
namespace YM.CF.Merino.Corolla
open Finset Lattice RG Scree Skye Vow
open scoped Topology Classical Matrix Matrix.Norms.L2Operator
open Cadre Sour Push.AbsoluteSums.Trees Vow.TreasuryFog
open Cube Stax Mew Fock
open scoped YM.CF.Mew

variable {I:Type}[LinearOrder I][Fintype I]
variable {n:Side}{P:BudgetPoint}{q:ℕ}{h:ℝ}

open Rill Rue

open Py Nor Ione

open Bake
variable {σ:I→Seat n}{y:I→Bag n}{c d:I→Aura n→ℝ}
variable (k:Sep P q h σ y c d)(τ:Ids n)(i:I)
abbrev nerve(X:Aura n): Copy n:=(k.biasH i).payX X ∅ X 1
def stems: RegBudget n := fun X=> if X.val.1 = σ i then
   (fun U=> nerve k i (lagE X) (U,τ)) else 0

include k
lemma collapse(X:Aura n)(V:Orbit n):
 tipI (fun a=> k.stripe a X ∅ X 1 V) [i] = nerve k i X V:= by
 let g(a:Key I):= ∑j,a j • nerve k j X V
 have p(a:Key I): k.stripe a X ∅ X 1 V = g a:=by
   rw [Sep.stripe_formula,Finset.sum_apply]; rfl
 rw [funext p]
 have vg:Solvent 1 g:=Solvent.sum univ _ (fun j _=> by
   simpa only [lTerm,Fin.prod_univ_one] using
      (Solvent.term (fun _:Fin 1=>j) (nerve k j X V)))
 have v:= mitt vg.riv roots i
 have q(a:ℂ):g (Function.update (0:Key I) i a)=a • nerve k i X V:=by
   unfold g; rw [sum_eq_single i]
   · rw [Function.update_self]
   · intro j _ p; simp [Function.update_of_ne p]
   simp
 rw [funext q] at v
 change cutI g i 0=_
 exact v.unique (by simpa using (hasDerivAt_id' (0:ℂ)).smul_const (nerve k i X V))


lemma shush : SpanTip P (stems k τ i) (σ i) k.stripe τ i := by
 refine ⟨fun X U _=>?_,fun X U _ g=>?_⟩
 · unfold stems; rw [collapse]; split <;> rfl
 rw [collapse,nerve,k.back i _ _ _ _ g]; rfl

variable(u:3≤P.B)(v:0≤h)
include u v
lemma fresh (X:Aura n):
 Medal P X.val ∅ (oV (fun U=>nerve k i X (U,τ))) h (d i X):=by
 have w:= (beer X (k.biasH i) (k.fire i X) v u (d:=d i)).merit
 convert w using 1; funext U
 exact Stax.opva _ U _ (fun J Y p=> (k.fire i J).tube.clean Y p) τ X X _ _ rfl

def wagesU(P:BudgetPoint)(i:I)(σ:I→Seat n)(d:I→Aura n→ℝ)(X:Scree.Hub n):ℝ :=
 if X.val.1=σ i then fareX P.B P X.val.2 * d i (lagE X) else 0

lemma wick (X:Scree.Hub n):
 PressB P X (stems k τ i X) h (wagesU P i σ d X):=by
 unfold stems wagesU; split
 · exact Medal.preservesE τ (fresh k τ i u v (lagE X)) v _
 exact Vale.rinse ..
omit u v
def nectar(P:BudgetPoint):ℝ:=Nor.reserveT P.power P.order P.B (P.B:ℝ)⁻¹

omit k in
lemma nectar_n (P:BudgetPoint):0≤nectar P:=by
 have :=bpos P; unfold nectar reserveT coin_n stilK; positivity

local notation "Y:" X:max=> nectar P*(d i X*Sour.tact (eighth P.B) P.B X)
lemma sweet (a:P.supportExponent≤1)(x:Seat n):
 (∑ j:Scree.Hub n, if x=j.val.1 then P.mass j.val.2 (wagesU P i σ d j) else 0) ≤ nectar P*voyageB (d i) P.B (eighth P.B):= by
 rw [←sum_filter,voyageB,mul_sum]
 let z:=univ.filter (fun j:Scree.Hub n=> x=j.val.1)
 suffices u: (∑ j∈z,P.mass j.val.2 (wagesU P i σ d j)) ≤∑ l ∈ z.image lagE, Y:l from
   u.trans (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun l _ _=>mul_nonneg (nectar_n _) (mul_nonneg (k.sign i l).2 (Real.exp_pos _).le)))
 have hi: Set.InjOn (@lagE n) (↑z):=by
   intro j t j' t' e
   exact Subtype.ext (Prod.ext (((mem_filter.mp t).2:x=j.val.1).symm.trans (mem_filter.mp t').2) (congrArg Subtype.val e))
 rw [Finset.sum_image hi]
 apply sum_le_sum; intro j _
 have w:0≤Y:(lagE j):=mul_nonneg (nectar_n _) (mul_nonneg (k.sign i _).2 (Real.exp_pos _).le)
 unfold wagesU RG.BudgetPoint.mass; split; swap; rw [mul_zero]; exact w


 let N:ℝ:=coverNumber P.B j.val.2
 calc
   _ ≤ Real.exp (P.supportExponent*N)*(nectar P*Real.exp ((P.B:ℝ)⁻¹*N)*d i (lagE j)) :=
      mul_le_mul_of_nonneg_left
       (mul_le_mul_of_nonneg_right (coinPay P j.val.2 _ (puck P).1.1) (k.sign i _).2)
       (Real.exp_pos _).le
   _ = (nectar P*d i (lagE j))*Real.exp ((P.supportExponent+ (P.B:ℝ)⁻¹)*N) := by rw [add_mul, Real.exp_add]; ring
   _ ≤ _ := by
      rw [←mul_assoc (nectar P)]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (nectar_n _) (k.sign i _).2)
      apply Real.exp_le_exp.mpr; unfold eighth; rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by linarith only [a,(puck P).1.1]) (Nat.cast_nonneg _)

include u v
lemma hive (a:P.supportExponent≤1):
 IncX primeU (stems k τ i) P h (nectar P*voyageB (d i) P.B (eighth P.B)):=⟨⟨wagesU P i σ d,wick k τ i u v,sweet k i a⟩,fun _ f=> False.elim f⟩
end YM.CF.Merino.Corolla

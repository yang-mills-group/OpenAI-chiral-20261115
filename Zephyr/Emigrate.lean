import Zephyr.Twice
import Zephyr.Season

/-! Per-incidence conversion for the (124) seasons. -/
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

open Py
/-- Explicit per-anchor price, Q w₀ times constant
(depending on the cover cutoff K and requested rate increment a/b). -/
def ticket124 (K:ℕ)(a:ℝ)(q w0:ℝ):ℝ:=
  ((Real.exp (a+1)+Real.exp K)*2+1) * (q*w0)

structure Claim124 (P:BudgetPoint)(v:Scree.Hub n→ℝ)(K:ℕ)(q w0 a:ℝ):Prop where
  anchored: Tab rootAt footing v P.B (1+(a+1)/(P.B:ℝ)) (ticket124 K a q w0)
  incidence: Touch footing v P.B (1+a/(P.B:ℝ)) (taxB P.B*ticket124 K a q w0)

theorem emigrate {x u:ℝ}
    (hc:P.supportExponent=1) {v:Scree.Hub n→ℝ}
    (T:DualBill P h X v x (Real.exp K*x+u))
    {q w0:ℝ} (q0:0≤q) (w1:1 ≤ w0)
    (t0:0 ≤ x)(t1:x ≤ 2*(q*w0))
    (d:Real.exp (-(P.B:ℝ)/2)*u ≤ q)
    (a:ℝ)(ha:0≤a)(he:a+1≤(P.B:ℝ)/2) :
    Claim124 P v K q w0 a:=by

 have y:= Tab.bridge T.pos T.low T.raised (add_nonneg ha zero_le_one) he P.B_pos
 rw [hc] at y
 have hx : Tab rootAt footing v P.B (1+(a+1)/(P.B:ℝ)) (ticket124 K a q w0):=by
    refine y.mono ?_
    have e : Real.exp (-(P.B:ℝ)/2) ≤ 1:= Real.exp_le_one_iff.mpr (by linarith only [Nat.cast_nonneg (α:=ℝ) P.B])
    rw [mul_add (a:=Real.exp (-(P.B:ℝ)/2))] -- tune
    unfold ticket124
    linarith only [
      mul_le_mul_of_nonneg_left t1 (Real.exp_pos (a+1)).le,
      (mul_le_of_le_one_left (mul_nonneg (Real.exp_pos (K:ℝ)).le t0) e).trans
         (mul_le_mul_of_nonneg_left t1 (Real.exp_pos (K:ℝ)).le),
      d.trans (le_mul_of_one_le_right q0 w1)]
 refine ⟨hx,Tab.touch T.pos (O:=rootAt) (fun i=> i.property) ?_ (by unfold ticket124; have := zero_le_one.trans w1; positivity) P.B_pos⟩
 rwa [add_div,←add_assoc] at hx
#print axioms emigrate
end YM.CF.Zephyr

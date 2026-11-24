import SatinThinPlaza
import Zephyr.Lit
import Zephyr.RegUpgrade
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Zephyr
open Pitching Focus QuadClock Vow

variable {m:Side}{D:Patch}{x h:ℝ}{A:GramM m}{v:Scree.Hub m→ℝ}

def price124 (D:Patch)(x:ℝ)(b:ℕ):ℝ:=
  chi_f 6 * (taxB b * ticket124 (hardEdge D) 10 (q124 D.L x) (w124 x))

/-- (124), including all its lit payments even on larger (final) footprints.
`footing` tests the entry support itself. -/
theorem Record124.lit124 (r:Record124 D x h A v):
  ∃ w:Scree.Hub m→ℝ, (∀ i,w i = chi_f 6 * v i) ∧
     (∀ i, LitReg A.p i.val.2 (head_L A.F i) h (w i)) ∧
     Touch footing w A.p.B (1+10/(A.p.B:ℝ)) (price124 D x A.p.B):= by
 let w(i):= chi_f 6 * v i
 refine ⟨w,fun _=>rfl,fun i=>?_,?_⟩
 · have t:=consult_bill (r.payment.reg i) (zero_le_one.trans r.height)
   rwa [r.order] at t
 have ha:= ((r.raised 10 (by norm_num) (by
    have z:(22:ℝ) ≤ A.p.B:=by exact_mod_cast r.twentyTwo
    linarith only [z])).incidence)

 intro o
 apply le_trans _ (mul_le_mul_of_nonneg_left (ha o) (spicy_f 6))
 rw [mul_sum]; exact sum_le_sum fun i _=> le_of_eq (by unfold due w; ring)
#print axioms Record124.lit124
end YM.CF.Py.Rate

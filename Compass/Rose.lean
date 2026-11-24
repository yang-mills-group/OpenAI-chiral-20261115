import Compass.West
import YM.CF.Ione.Tape
import Compass.Entire
import Compass.Colors
import YM.CF.Ione.Rank
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Links
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Compass
open Ione
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
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}
open Vow Salt
variable (P:BudgetPoint)(s:Sweep n)
local notation "Ta"=> actY s
local notation "HQ"=> (hail_Q s).val
local notation "Φg"=> (Finset (Dwell n))
open Nacre
abbrev MirrorFit (s:Sweep n): Prop:= s.charge=false∧ Anchored s.s
lemma MirrorFit.inv(t:MirrorFit s): MirrorFit s⁻¹:=⟨t.1,t.2.rev⟩
lemma shiny (t:MirrorFit s):Moncol (hail_Q s).val:=by
 let c:=spinU s.charge s.s
 apply Moncol.wedges (M:=(praise s).val)
 apply spicy; apply ayes; let h:s.charge=false:=t.1; apply monJet _ s.s (detX s.s) t.2; have h1:JetS s.s s.charge (detX s.s) (spinU s.charge s.s):=spinZ ..; rw [h] at h1 ⊢; exact h1
lemma pullPress {F:InkD n}(p:Scree.Hub n)(u:MirrorFit s)(t:PressB P (moveHub s p) F h c)(x:0≤h): PressB P p (step_F s F) h (duty_Q P.order P.power*c):=feastB P s p (shiny _ (u.inv _)) t x
lemma pullMedal {F: Copy n}(X D: Support (More n))(u:MirrorFit s)(p:Vow.Medal P (actY s X) (actY s D) F h a)(hv:0≤h): Vow.Medal P X D (turn_V s F) h (strive_E P.order*a):=feastX P s X D (shiny _ (u.inv _)) p hv
lemma rains (t:Anchored s.s) : Moncol (hail_Q s).val:=Moncol.wedges (M:=(praise s).val) (spicy _ (ayes _ (fullJet _ s.s _ _ t (spinZ ..)) (castX s) _) _)
lemma pullPressR {F:InkD n}(p:Scree.Hub n)(u:Anchored s.s)(t:PressB P (moveHub s p) F h c)(x:0≤h): PressB P p (step_F s F) h (duty_Q P.order P.power*c):=feastB P s p (rains s⁻¹ u.rev) t x
lemma pullMedalR {F: Copy n}(X D: Support (More n))(u:Anchored s.s)(p:Vow.Medal P (actY s X) (actY s D) F h a)(hv:0≤h): Vow.Medal P X D (turn_V s F) h (strive_E P.order*a):=feastX P s X D (rains s⁻¹ u.rev) p hv
#print axioms pullMedal
end YM.CF.Compass

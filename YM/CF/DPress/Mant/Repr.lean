import YM.CF.DPress.Mant.Nar
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open Larch DPress.Analytic Salt Oise Moral LinearT -- nar import.F.R
variable {J:Type*}{n:Side}{h s a p t:ℝ} (W:ℂ→ J) (Z₀ Z₁:J→ Pax n) (V:Orbit n)(P:BudgetPoint) (q:∀ i:J,Wisp P (Z₀ i) (Z₁ i) h s a p) (r:Hues.Prosper t (Z₀∘W))(c:Hues.Prosper t (Z₁∘W))(v:1≤h)(hV:V.1=1)(w:1<t)
abbrev dFj(i:J): Aura n→ℝ:=curr_r P (Z₁ i) (Z₀ i) V -- tune
abbrev DBj (i:J): Pax n:=curr_X P (Z₁ i) (Z₀ i) V
include r c q v hV w
lemma representLb(i:Skye.Seat n): tallB (fun x=>|(dFj Z₀ Z₁ V P (W 1)- dFj Z₀ Z₁ V P (W 0)) x|) P.B (P.supportExponent+1+1) i ≤ 2*p/(t-1) := Hues.diff_w (Z₀∘W) (Z₁∘W) V (fun i=> q (W i)) v w hV r c i
lemma presentLb: PactF P (P.supportExponent+1+1) h (DBj Z₀ Z₁ V P (W 1)-DBj Z₀ Z₁ V P (W 0)) (6*(p/(t-1))):= Hues.payout (Z₀∘W) (Z₁∘W) V (fun i=> q (W i)) v w hV r c
omit c q hV
lemma gainLb(q:∀ i, PactF P a h (Z₀ i) p)(c:0≤ a): PactF P a h (Z₀ (W 1)-Z₀ (W 0)) (p/(t-1)):= wage_c (n:=n) P h a c v (Z₀ ∘ W) (fun i _=> q (W i)) (fun i y _=>r i y) w -- tune
omit r v w
lemma pressC1(W:ℂ→J)(f:J→Cusp n)(P:BudgetPoint)(r:∀ (i:Aura n) (j:Hub0 n) (V:Orbit n),DifferentiableOn ℂ (fun z=> f (W z) i j V) (ank t))(v:1≤h)(w:1<t)(q:∀ i,XL P h a (f i) p)(c:0≤a) : XL P h a (f (W 1)-f (W 0)) (p/(t-1)):= Ξcare P h a true v c (f ∘ W) (fun i _=> q (W i)) (fun i j _ V _=>r i j V) w
end YM.CF.Py.Kay

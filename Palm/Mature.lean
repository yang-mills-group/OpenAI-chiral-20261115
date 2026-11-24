import YM.SU5.Fineness.Driving
import Thin.Cred
import YM.CF.Brood.Hara
set_option autoImplicit false

set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
open Cascade Fief Wray Oath Feu Feu.Corset Beau Haro Ione Salt
open Roots Mew Neon Rate Pitching Pitching.Focus

variable {R:Patch}{K:Teller SU.group}{L:ChartRatio SU.group}
theorem Ready_K.eventual (L:Side) :∀ᶠ x in atTop,Ready_K L x:=by
 obtain ⟨x,u⟩:=eventually_atTop.mp (((Work.E01.radiusB_tendsto.eventually_ge_atTop (L.val+10)).and (Extra.Iteration.Rebuild.geometry (Vale.billX L))))
 filter_upwards [eventually_ge_atTop x] with y uY
 refine ⟨fun i p=>Nat.le_trans (by omega) (u i (uY.trans p)).1,fun i p=>?_,fun i p=>(u i (uY.trans p)).2.1.1⟩
 let x:=radiusB i; have he:L.val+1≤ x:=(show L.val+1≤ L.val+10 by omega).trans (u _ (uY.trans p)).1; have hv:10 ≤ x:=Nat.le_trans (by omega) (u _ (uY.trans p)).1; unfold Roots.cape_B; have ht:= Nat.mul_le_mul_right (4*x+2) he; change (L.val+1)*(4*x+2) + 2*x ≤ x+x^3; apply le_trans (Nat.add_le_add_right ht _); have hq: 10*x^2≤ x^3:=by nlinarith;
 nlinarith

lemma largeEligible (Z:Grace K R L)(G:Morn K)(X:Diary)(P:X.fits R){qv Aρ ε:ℝ}(l: Καlendar R G.armor qv Aρ G.Mult ε)(x:ℝ):
 ∀ᶠ j in atTop, let xk:= Vale.hat R.L x j; Ready_K R.L xk ∧ Lens_K R G.cap (PongR R.L) (pass_C R.L qv) xk (X.Z xk) (X.W xk) (X.V1 xk) (X.KR xk):=by
 let hq : Read_V R (Lens_K R G.cap (PongR R.L) (pass_C R.L qv)):= nut_V _ _ (pay_g _ _ l.asp.pay |>.2) (book_ε R.L|>.1) _
 let hu := (Ready_K.eventual R.L |>.and (hq _ _ _ _ P))
 exact (stage_slope Z x).eventually hu
end YM.CF.Py

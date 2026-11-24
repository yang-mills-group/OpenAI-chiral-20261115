import Thin.UnOutlook
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
-- For fixed R. Smaller notation context
open Pitching Pitching.Focus
open Appel.Rate Stockpile
abbrev cappedBar (c:Estimate)(X:ℝ→ℝ)(x:ℝ):= 4*(c.F x+ X x)
abbrev raisedB (R:Patch)(c:Estimate)(X σ:ℝ→ℝ)(x:ℝ):= c.small x+2*σ x * value_ R x (X x)
structure WorkLend (R:Patch)(c:Estimate)(X σ:ℝ→ℝ)(x:ℝ) : Prop where
 above : 2*c.F x≤ cappedBar c X x
 newbar : 2*X x≤ cappedBar c X x
 future : degreePrice (radiusB x) (cappedBar c X x) 1<1
 now : 0<c.F x
 cold : 0<X x
 heat : 2*σ x * rainX R 2 x≤ 1
 short : 1≤ rainX R 1 x
 comp : rainX R 1 x≤ rainX R 2 x
open Nor
lemma affordLend (R:Patch)(c:Estimate)(X σ:ℝ→ℝ)(hh:c.Economic R)(ru:warmK c.F)(rd:warmK X)(d:sizeK R.L 1 X)(e:sizeK R.L 3 σ):
    sizeK R.L 1 (cappedBar c X) ∧warmK (cappedBar c X)∧sizeK R.L 3 (raisedB R c X σ)∧∀ᶠ x:ℝ in atTop, WorkLend R c X σ x:= by
 let h0: sizeK R.L 1 (cappedBar c X):=(hh.F.accrue d).scale 4
 have h1:∀ᶠ x in atTop,0<cappedBar c X x:= (ru.and rd).mono (fun x ⟨u,v⟩=> mul_pos (by norm_num) (add_pos u.1 v.1))
 have u1:= Stockpile.feeWarm h0 h1
 have ht:= Stockpile.valueK d rd
 let h2: sizeK R.L 3 (raisedB R c X σ):= hh.small.accrue (((e.scale 2).tint ht).low (by omega))
 have H: sizeK R.L 1 (fun x => rainX R 2 x * (2*σ x)):=Wray.rockP 2 (e.scale 2)
 refine ⟨h0,u1,h2,?_⟩
 filter_upwards [ru,rd,u1,H.spine.eventually (ge_mem_nhds (by norm_num:(0:ℝ)<1)), (Scales.year SU.group R.L).eventually_gt_atTop 0,(Scales.minute SU.group R.L).eventually (gt_mem_nhds (by norm_num:(0:ℝ)<1))] with x v w cH p vY vG
 have hcv:= v.1; have hQ:=w.1
 refine ⟨?_,?_,lt_of_le_of_lt cH.2 (by norm_num:(1/2:ℝ)<1),hcv,hQ,mul_comm (2*σ x) _ ▸ p, ?_,?_⟩
 · unfold cappedBar; linarith only [hcv,hQ]
 · unfold cappedBar; linarith only [hcv,hQ]
 · exact Wray.rain_one _ _ vY vG.le
 have he:= Scales.gauge SU.group R.L vY
 unfold rainX; exact inv_anti₀ (by positivity) (pow_le_pow_of_le_one he.le vG.le (by omega))
end YM.CF.Py.Rate

import YM.CF.DPress.Loch.Dolly
import YM.CF.Reed.Trio
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
open Oise
variable
 {N P B:Side}{S:StepData (Domain N B) (Domain P B)}{G:Ratio (mid N B) (mid P B)}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group} {d:ℝ} {V:Grace K R L} {U:Grasp V.U B d}{W:GivenX V U}
 (C:Tew W)
-- Planet.Space estimates. Use across all LPC.
structure Income0 (O:ℝ→ Shore0) (w:ℝ→ℝ):Prop where
 stone : ∀ t, (O t).δ=w t
 z : sizeK R.L 1 fun i=>(O i).z
 s : sizeK R.L 1 fun i=>(O i).s
 D : sizeK R.L 3 fun i=>(O i).D
 K : sizeK R.L 3 fun i=>(O i).K
 Vt : sizeK R.L 1 fun i=>(O i).Vt
 Pt : Litt R 2 fun i=>(O i).Pt
 degree : ∀ᶠ x:ℝ in atTop,0< (O x).z∧ degreePrice (radiusB x) (O x).z 1 ≤ 1/2
 Wish : ∀ᶠ x in atTop, Pony x C (O x)
lemma Tew.opening (w:ℝ→ℝ) (t:sizeK R.L 2 w)(g:∀ i,0≤w i) :∃ O:ℝ→ Shore0, Income0 C O w:=by
 obtain ⟨z,D,H',Qh,Fκ,Xr,hz,-,hv,hH,hQ,hκ,hX,Qht,cX⟩:= C.creek.block w w w w t t t (t.low (by decide))
 let O (x:ℝ) : Shore0 := ⟨w x,z x,H' x,D x,Fκ x,Xr x,Qh x,Qht,g x⟩
 refine ⟨O,(fun t=>rfl),hz,hH,hv,hκ,hX,hQ,(cX.mono fun x p=>⟨p.2.1,p.2.2.1⟩),?_⟩ -- Prop nested
 filter_upwards [cX,(Scales.year SU.group R.L).eventually_gt_atTop 0,Work.E01.radiusB_tendsto.eventually_ge_atTop (C.M₀+C.M₀),progP C.p C.i 100] with x p ν f v
 refine ⟨ν,f,fun i=> p.1 i,v,?_⟩; intro M0 P G S Q
 obtain ⟨M,Hm,PP,tη,ht,α,Qb,Jz,Ψ⟩:= p.2.2.2 S G Q.T Q.G₀ Q.G₁ Q.X Q.Y Q.A₀ Q.A₁ Q.Joint Q.baseL Q.stat Q.large
 obtain ⟨tz,tq,-⟩:= Ψ 1 0 0 0 0
 refine ⟨⟨M,Hm,PP,tη,ht,α,Qb,Jz,tz,tq,?_⟩⟩; intro β F0 J k u X' Y' _ D'; exact (Ψ β F0.1 0 F0.2 J).2.2 (show StatV V G Q.T U W X' Y' _ _ C.w x C.p C.i from by unfold X' canopy; rw [tz,tq]; exact store Q.stat u) (arcL C.uB k) D' -- unfolding issue key
end YM.CF.Py.Kay

import YM.SU5.FiniteGaugeData.Marked.Journey.Wake
set_option autoImplicit false
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
open Ione Beau Haro Cascade Fief VolumeRate
open LocalLimit
namespace Decaf
open Donor Preparation
variable {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}{V:Grace K R L}{e h hβ t:ℝ}{m B:Side}{P:Grasp V.U B e}{W:GivenX V P}{N:ℕ}(T:Month t 1 6 2 N V W)(C:ℝ→ℝ)(τ:ℝ)
lemma topdeck (S:ℝ) (i b:ℕ) (δ:ℝ)(hd:0<δ) : ∀ᶠ n in atTop, ∀ m:Side, cone b n m→ Real.exp (S * game m)* divisionBill T C τ i n m ≤δ:=by
 let a:= volumePrice T i+1; let t0:= thermalCost C R t τ i * postage B R.L i; let t1:= (expense C R t τ i+|serviceCost T i|)*postage B R.L i
 have p:=collapse b (c:=Real.log 2) (Real.log_pos (by norm_num)) (half_pos hd) (horizontalPrice T i)
 filter_upwards [p (a+t0+S), p ((a+t0)+t1+S)] with n h0 h1 m u
 specialize h0 m u; specialize h1 m u
 let D:= horizontalPrice T i * decay n (Real.log 2); let N:=game m; let v:=Real.exp (a*N); let w:=Real.exp (t0*N); let x:=Real.exp (t1*N); let y:=Real.exp (S*N)
 have hx: D*(v*w*y) ≤ δ/2 := by simp only [add_mul,Real.exp_add] at h0; exact h0
 have hy: D*(v*w*x*y)≤δ/2:=by simp only [add_mul,Real.exp_add] at h1; exact h1
 unfold divisionBill outage; rw [sites_postage,←mul_assoc (thermalCost ..), ←mul_assoc (_+|serviceCost ..|)]
 change y*((1+x)*(D*v)*w) ≤ _
 linarith only [hx,hy]
#check cone
#print axioms topdeck
end Decaf
end YM.CF.Py.Rate
end

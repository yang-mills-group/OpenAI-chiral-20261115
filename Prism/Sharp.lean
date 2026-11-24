import Prism.Fares
import Prism.Sums
import Taffeta.Silk
import YM.SU5.FiniteGaugeData.Pannier.Sketch
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
open Roots Buffered LocalLimit LocalLimit.Papal Dyad Dyad.Keeping Mew Compass Drift
attribute [-instance] instDecidableEqLex
set_option quotPrecheck false
namespace Decaf
variable {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}(V:Grace K R L){e h:ℝ}{m B:Side}{P:Grasp V.U B e}(W:GivenX V P)
open Preparation Afterglow
variable {Xθ:Preparation}{l:ℕ}(a:Preparation.Course Xθ (VolumeCape.Dream.Nimbus l))
abbrev cupcost (Xθ:Preparation)(τ:ℝ)(mΨ:ℝ)(meter:ℕ→BudgetPoint)(j:ℕ):ℝ:=
  let L:= Xθ.R.L; let y:= Vale.hat L Xθ.x j
  |earnings Xθ.W (meter j) (2*y) (dleaf L y+mΨ*allotΨ L y)| + |expense Xθ.C Xθ.R Xθ.x τ j|
lemma cityfare (mΨ Aα:ℝ)(u:0 ≤ mΨ) (s i k:ℕ)(v:s≤a.uv k)(w:(a.voyage i).kick≤k){I:Type}[Fintype I][LinearOrder I](o:I → Site (count a s i))(T:Log I (count a s i))
  (he:Candle Xθ.V (Parcel.booksW (a.voyage i).funds (a.uv k) ((a.voyage i).X (a.uv k))) Xθ.h Aα mΨ s o T)(l:List (PairKey I)) :
    ‖rumor Xθ.V (Parcel.booksW (a.voyage i).funds (a.uv k) ((a.voyage i).X (a.uv k))) s T l 1‖≤ Real.exp (cupcost Xθ a.τ mΨ a.meter.a s * sites (count a s i)):= by
  obtain ⟨f,g,r,hy,H⟩:=prices_plot a s i k v
  let C:= gram a s i k
  let Vk:= Xθ.V; let ap:= a.voyage i; let A:=ap.X (a.uv k)
  let L:= Xθ.R.L; let y:=Vale.hat L Xθ.x s; let d:= dleaf L y; let h:= room a s i
  let q:= allotΨ L y
  have Hp:Xθ.U.roundZ ≤ (count a s i).val:= Xθ.J.gran.trans (ap.ownership s).size
  have p: Clinic o T 1 Xθ.h (Aα*q) (mΨ*q) C L (soot q):=he
  let F:= earnings Xθ.W C.p (2*y) (d+mΨ*q)
  let X:= expense Xθ.C Xθ.R Xθ.x a.τ s; let n:=sites (count a s i)
  have hX:0 ≤ n:=zero_le_one.trans (sites_pos _)
  have ht(Zz:Key (PairKey I))(Wt:Zz∈Mew.hill (PairKey I))(x:Orbit (count a s i)): ‖Graph.recX Xθ.U (markedB T C Zz) h x‖≤ Real.exp (F * sites (count a s i)):=by
      apply coarseBill Vk Xθ.W o T C Xθ.J.n (a.uv k-s) (roofage a i s) Hp Xθ.height p g r hy _ H _ Wt _ x
      · exact (zero_le_one.trans a.oneP).trans (Vale.crown ..)
      · -- q≥0 & mΨ h
        exact mul_nonneg u (sq_nonneg _)
  have hs:= level_secured _ A a.τ a.revenue (ap.lower k w) s v
  have eL:= bound_clover Xθ.V (G:=h) o T C p ht hs l
  refine eL.trans (Real.exp_monotone (show F*n - -X*n ≤ cupcost Xθ a.τ mΨ a.meter.a s * n from ?_)) 
  rw [show cupcost Xθ a.τ mΨ a.meter.a s=|F|+|X| from (by unfold F; change C.p=_ at f; rw [f]),add_mul] -- reverse? RHS already add_mul, want expand
  have h1:=mul_le_mul_of_nonneg_right (le_abs_self F) hX; have h2:=mul_le_mul_of_nonneg_right (le_abs_self X) hX; linarith only [h1,h2]
#print axioms cityfare
end Decaf
end YM.CF.Py.Rate
end

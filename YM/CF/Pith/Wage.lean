import YM.CF.Pith.Site
import YM.CF.Pith.Rime
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Jade
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
variable (F:Pilot)(Z:Pluck R) (I: Stake.Isle){σ:ℝ}(Q: Tun I Z F σ){H:Muster G S x d T}
open Vow Bake Lilt Nor SupportP
lemma around_B(t:ℕ) : BoreP fun x=>(around_x t (radiusB x):ℝ) :=by unfold around_x; push_cast; exact ((BoreP.still _).grip (((BoreP.still 4).grip BoreP.radius_c).join (BoreP.still _))).join ((BoreP.still _).grip BoreP.radius_c)
lemma ear_B(t:ℕ) : BoreP fun x=>(ear_p (porch_i t (radiusB x)):ℝ):=by
 have he:BoreP fun x=> (porch_i t (radiusB x):ℝ):=by simpa [porch_i,around_x] using ((((around_B t).join (around_B t)).join (BoreP.still (1:ℝ))).self 4)
 simpa [ear_p,porch_i,around_x] using (((BoreP.still 1).join he).join (he.self 2))
variable(W a c b:ℝ)(hv:b>0)
include hv
lemma spirit_t(k j n:ℕ): ∃ p:ℕ,∀ m:ℕ,p≤ m → Litt R 2 (fun x=>(ear_p (porch_i Z.N1 (radiusB x)):ℝ) * |costC Z.N1 (radiusB x) k j n a (roseP F Z I Q x (luceL R m x) k W b c)|):=by
 obtain ⟨p,F'⟩:=locust F Z I Q b c W hv k; refine ⟨p,fun m h=>?_⟩
 unfold Lilt.costC; exact beam_v (ear_B Z.N1) (Litt.abs_t ((beam_v (Nor.vale_u n k _) ((F' m h).scale_l _)).scale_l _))
omit hv
lemma rain_l(R:Patch)(k:ℕ):sizeK R.L k (fun x=> (rainX R k x)⁻¹):=by unfold rainX; simp only [inv_inv]; simpa only [one_mul] using (sizeK.main R.L).square k
variable {f:ℝ→ℝ}(T':∀ᶠ x in atTop,0 < f x∧ degreePrice (radiusB x) (f x) 1≤1/2)
include T'
lemma ample_b (p:sizeK R.L 1 f)(k' j n:ℕ)(A:ℝ):sizeK R.L (n+1) (fun x=>grain_q (radiusB x) k' j A (f x) n):= (prism_k (ε:=A) p k' j T').scale _
lemma lean_q(p:sizeK R.L 1 f)(k' j:ℕ)(A:ℝ):sizeK R.L 3 (fun x=> tilt_Q (radiusB x) k' j A (f x) (rainX R 2 x) (rainX R 1 x)):= ((sizeK.tint (rain_l R 2) (ample_b T' p k' j 0 A)).accrue ((rain_l R 1).tint (ample_b T' p k' j 1 A))).accrue (ample_b T' p k' j 2 A)
end YM.CF.Jade

import YM.CF.Jade.Prune
set_option autoImplicit false
set_option maxHeartbeats 400000
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
variable{r:ℕ}
local instance :MeasurableSpace (Finset (Sat S)):= ⊤
local instance :MeasurableSingletonClass (Finset (Sat S)):=⟨fun _=>trivial⟩
local instance :MeasurableSpace (List (Hos S r)):= ⊤
local instance :MeasurableSingletonClass (List (Hos S r)):=⟨fun _=>trivial⟩
local instance :Finite ↥(Sil S r):=Set.Finite.to_subtype sill_p
local notation "Sν"=> (Sil S r)
local notation "ΦT"=> (tale S k t)
local notation "dP"=> Directions SU.group (Domain P B)
open Girt Plume
local notation "βX"=> (FilonType) -- dummy
abbrev stamp (x:Cord S)(k:ℕ)(b:ℝ)(r:ℕ): ↥(Sil S r) × ↥(tale S k b):=(era x.2.2,velt x.2.1.2 k b)
lemma stamp_m: Measurable (fun x:Cord S=>stamp x k t r):= (sill_m.comp measurable_snd.snd).prodMk (velt_m.comp measurable_snd.fst.snd)
variable{E:Type}[MeasurableSpace E][Finite E][MeasurableSingletonClass E]{F:Type}[MeasurableSpace F](μ:Measure F)[IsFiniteMeasure μ]
lemma rate_m{H O:Type}[LinearOrder H][Fintype H](W: Raid H)(T:E→Track O (Raid H))(φ:F→E)(p:Measurable φ) (i:O): rateT W (fun t h=>∫ j,T (φ j) t h∂μ) i=∫ j,rateT W (T (φ j)) i∂μ:=by
 unfold rateT joinV; rw [MeasureTheory.integral_finsetSum]; refine sum_congr rfl fun x v=>(MeasureTheory.integral_const_mul _ _).symm; exact fun k _=> frill _ p (fun y:E=>W k*T y i k) μ
lemma invoiceW {u:ℝ}(T:E→Track (Crowd (Site N)) ℝ)(φ:F→E)(p:Measurable φ)(o:Site N): invoiceB k u o (fun i=>∫ z,T (φ z) i ∂μ)=(∫ z,invoiceB k u o (T (φ z))∂μ):=by
 unfold invoiceB; rw [MeasureTheory.integral_finsetSum]; swap; · exact fun i _=>frill _ p (fun x:E=> if o∈ i.val then T x _*_ else 0) μ
 refine sum_congr rfl fun i g=>?_ ; by_cases v:o∈ i.val; · simp_rw [if_pos v]; rw [MeasureTheory.integral_mul_const]
 simp_rw [if_neg v]; rw [integral_zero]
lemma invoice_m {u:ℝ}(o:Site N)(T V':Track (Crowd (Site N)) ℝ)(p:T ≤ V'):invoiceB k u o T ≤ invoiceB k u o V':=by unfold invoiceB; apply sum_le_sum; intro i _; split_ifs; exact mul_le_mul_of_nonneg_right (p _) (Real.exp_pos _).le; exact le_rfl
end YM.CF.Jade

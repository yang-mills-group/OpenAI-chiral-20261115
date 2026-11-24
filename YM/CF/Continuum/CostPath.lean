import YM.CF.Song.Height
import YM.CF.Song.Fish
import YM.CF.Song.Beat
import YM.CF.Sere.Uinta
import YM.CF.Continuum.Beluga
import YM.CF.Continuum.Saloon

-- Combine extensive charges for a Loom step with an actual occupancy pre-budget.
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
open Jade
open Ione Lilt Nor Larch Beau Vow Sour Glyph
open Earn
abbrev curve_F (Z: Side)(B D:Side) (x C : ℝ): ℝ:= pathFees B D (Scales.y SU.group Z x) C
variable (omg F:ℝ→ℝ)(eK:BudgetPoint)
lemma advance_E (homg:sizeK R.L 2 omg)(hq:sizeK R.L 1 F) (q:Clip)(σ C Aχ Γχ:ℝ): ∀ᶠ i in atTop, let z:= hall_P eK i; (tax_E z q σ C Aχ Γχ+1)*omg i+ F i*(1-degreePrice (hall_P eK i).B (F i) wΨ)⁻¹ ≤ 1:= by
 let K:=tax_E eK q σ C Aχ Γχ; let β(i):= (1-degreePrice (hall_P eK i).B (F i) wΨ)⁻¹; have he: Tendsto β atTop (𝓝 1):=by simpa only [sub_zero,inv_one] using! ((tendsto_const_nhds (x:=(1:ℝ))).sub (fee_Q eK F hq|>.spine)|>.inv₀ (show (1:ℝ)-0≠0 by simp))
 have hx:Tendsto (fun i=> (K+1)*omg i+F i*β i) atTop (𝓝 0):=by simpa only [mul_zero,zero_mul,add_zero] using Tendsto.add ((homg.low (k:=1) (by omega)).spine.const_mul (K+1)) (hq.spine.mul he)
 filter_upwards [hx.eventually (ge_mem_nhds zero_lt_one)] with i b; intro z
 obtain ⟨x,y,p⟩:=let_X eK i; rw [spend_T eK _ _ _ _ _ z x y p]; exact b
section linepiece
variable {b f:Side}(S':StepData b f)(C₀ C₁ C g:ℝ)
local notation "Φ"=> roomSite b
local notation "Ψ"=> roomSite f
include S'
lemma cost_F (x:ℝ)(L:Side) : Real.exp (curve_F L b f x (C₁+C₀+|g|+1)) ≤ Real.exp (pathFees b f (Scales.y SU.group L x) C₁)*Real.exp (-Ψ*C₀-Ψ*g)*Real.exp (-Φ):=by
 rw [←Real.exp_add,←Real.exp_add]; apply Real.exp_monotone; let v:=Window.strengthLog (coupling (Scales.y SU.group L x)); have he:(0:ℝ)≤Ψ:= by unfold roomSite; positivity
 unfold curve_F pathFees; linarith only [mul_le_mul_of_nonneg_right (le_abs_self g) he, builtLe S']
end linepiece
#print axioms cost_F
end YM.CF.Py

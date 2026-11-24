import YM.CF.Nor.Pile
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Nor
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
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
local notation "B_"=> (More N)
local notation "S₁"=> (Domain N B)
local notation "dN"=> Directions SU.group (More N)
variable (P0:BudgetPoint) (o:Seat N) (X V_:Support (More N))(K_:ℕ)
-- aperture and endpoint charge recover polynomial (AFTER B). tunable after incoming. for any V_
variable(p₀:BudgetPoint)(U: Support (More N))(o:Seat N)(h:o∈U) -- remove
variable(H: Raid (Dwell N))
def liftR(k:ℕ)(a:ℝ):= composeCost p₀.order (p₀.order.factorial*a) (surgeL p₀ U k)
def linkY(k:ℕ)(i:Finset (Dwell N)):=if i ∈ Wheat (camp U) then liftR p₀ U k (H i) else 0
local notation "Z'"=> surgeL p₀ U k
local notation "Y_"=> (liftR p₀ U k 1)
include h
lemma rate_i(k:ℕ)(v:ℝ)(b:0 ≤ H)(p:0 ≤ v): (∑ i:Finset (Dwell N), Scree.tariff p₀ o v i * linkY p₀ U H k i) ≤ (surgeL p₀ U k*liftR p₀ U k 1)*joinV (stake v) H:=by
 let U':= liftR p₀ U k 1; let Z:=surgeL p₀ U k; have he:= rootA p₀ o U k h; have hu:0≤ U':=by unfold U' liftR Jet.composeCost; positivity
 unfold joinV; rw [mul_sum]; apply sum_le_sum; intro i _; unfold linkY; split; swap; · rw [mul_zero]; exact mul_nonneg (mul_nonneg (zero_le_one.trans he) hu) (mul_nonneg ((stokes p).fee _) (b _))
 rename_i hx; have ht:i⊆ camp U:= mem_powerset.mp (mem_filter.mp hx).1
 have hg : (1+(endL o i:ℝ))^p₀.power ≤ Z:=by
    let Ux:= coverNumber k U; have hk:endL o i ≤ Ux*(4*k+2)+2*k:= by refine Finset.sup_le fun a g=>?_ ; exact Corona.extent _ _ h ((mem_filter.mp (ht g)).2)
    unfold Z surgeL; gcongr; exact_mod_cast hk
 rw [Scree.tariff,show liftR p₀ U k (H i)=U'*H i from (by unfold U' liftR Jet.composeCost; ring)]; apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hg (pow_nonneg p _)) (mul_nonneg hu (b _))); unfold stake; dsimp only [Z,U'] at *; exact le_of_eq (by ring)
-- sign reconstruction ignores unsupported
include h
lemma tube_s (V:Pane N)(X: Finset (Seat N))(k:ℕ)(hX:V∈Rue.litres p₀.threshold U X)(F: Pane N→Cipher N)(v:∀ W, W∈ Rue.litres p₀.threshold U X→ Flour (camp U) (F W).val)(t:∀ i:Finset (Dwell N), Signs p₀ o ((fun v=>crumb (F v).val i)∘ gyrate (unrest X p₀.B) V) (liftR p₀ U k (H i))) (i:Finset (Dwell N)): Signs p₀ o ((fun v=>crumb (F v).val i)∘ gyrate (unrest X p₀.B) V) (linkY p₀ U H k i):=by
 unfold linkY; split; exact t _
 rename_i g; refine Prism.mint (Prism.hail (v:=(0:ℝ)) (show ‖(0:ℂ)‖≤0 from norm_zero.le)) ?_ -- tune binders
 let P:=Rue.litres p₀.threshold U X; let Y:= gyrate (unrest X p₀.B) V; filter_upwards [(show ∀ᶠ i in 𝓝 0, Y i∈P from (stickU ..).continuousAt.eventually ((Rue.open_l ..).mem_nhds (show Y 0∈P from (show Y 0=V from Forge.born (unrest X p₀.B) V).symm ▸ hX)))] with i' p; exact ((v _ p).door g).symm
-- further. pay polynomial weights
end YM.CF.Nor

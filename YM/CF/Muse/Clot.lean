import YM.CF.Muse.Earn
 
 
 
 
 
import YM.CF.Muse.Hours
set_option autoImplicit false
set_option maxHeartbeats 600000
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
variable {d e η t g A B':ℝ} {j k k' m n l:ℕ}
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
local instance clotP_P0 :MeasurableSpace (Finset (Sat S)):= ⊤
local instance clotP_P1 :MeasurableSingletonClass (Finset (Sat S)):=⟨fun _=>trivial⟩
local instance clotP_P2 :MeasurableSpace (List (Hos S r)):= ⊤
local instance clotP_P3 :MeasurableSingletonClass (List (Hos S r)):=⟨fun _=>trivial⟩
local instance clotP_P4 :Finite ↥(Sil S r):=Set.Finite.to_subtype sill_p
local notation "Sν"=> (Sil S r)
local notation "ΦT"=> (tale S k t)
local notation "dP"=> Directions SU.group (Domain P B)
open Girt Plume
open Lilt Feu Nor
open Nor
local notation "Kκ"=> pp
local notation "vQ"=> (radiusB x)
-- prune support Strung costs.Sec.Finished ledger weight 
local notation "sν"=> mid N B
variable(Aγ: Track (Ride S) (Raid (Dwell (mid N B))))

local notation "Qρ"=> (leaf (Site (Domain N B)))
variable (T₀ T₁ C:ℝ)(A0:Support (Domain N B))(B0:BudgetPoint)(p:B0.B=k)(θ:Seat (mid N B))(ζ₁:0 < T₀)(h0:0 ≤ T₁)
variable (W:ℝ)(hW:0 ≤ W)(hκ:0≤ Aγ)(vcT:Strung A0 (rateT (Scree.tariff B0 θ T₁) Aγ) k (B0.supportExponent+T₀+T₀) C) -- v name conflict
local notation "YE"=> (rateT (Scree.tariff B0 θ T₁) Aγ)
local notation "TΦ"=> rateT (Scree.tariff B0 θ T₁)
local notation "Ac"=> (coverNumber k A0:ℝ)
include hW hκ vcT p h0 ζ₁
lemma cone_m : let Y:= rateT (Scree.tariff B0 θ T₁) (raiseP B0 Aγ k); let A:= Real.exp (B0.supportExponent*coverNumber B0.B A0); (∑ j:Palot.leaf (Site (Domain N B)) with A0⊆ j.val, W*(coverNumber k A0:ℝ)* B0.mass j.val (Y (Stilo.beamH j.val))) ≤ W * backX T₀ * (leaps B0.order B0.power T₀ * C):=by
 intro Y A; let g:= bills B0 Aγ A0 (B0.supportExponent+T₀) C T₁ θ hκ h0 T₀ ζ₁ vcT -- tune order
 let I:= Finset.univ.filter (fun i:Palot.leaf (Site (Domain N B))=> A0⊆ i.val); let f:Palot.leaf (Site (Domain N B))→ Ride S:=fun i=>Stilo.beamH i.val
 have hp: Injective f:=fun i j d=> Subtype.ext (by let ht:= congr_arg Stilo.bay d; unfold f at ht; simpa only [bay_beam] using ht)
 have he:0≤ backX T₀:=inv_nonneg.mpr ζ₁.le; refine le_trans ?_ (mul_le_mul_of_nonneg_left g.pay (mul_nonneg hW he)); let P(x:Ride S):= Trees.currency k (B0.supportExponent+T₀) (Stilo.bay x)* Y x
 calc
    _ ≤ W*backX T₀ *∑ i∈I,P (f i):=by rw [mul_sum]; apply sum_le_sum; intro i h; have he:(coverNumber k A0:ℝ)*Trees.currency k B0.supportExponent i.val ≤ backX T₀ * Trees.currency k (B0.supportExponent + T₀) i.val:= (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Corona.cover_mono (mem_filter.mp h|>.2) k)) (Real.exp_pos _).le).trans (rayY T₀ ζ₁ k B0.supportExponent _); unfold P f; rw [bay_beam]; unfold BudgetPoint.mass; rw [p]; have V:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hW) (g.hand (f i)); simpa only [mul_assoc,Y,Trees.currency,f] using V
    _ ≤ _:=by change W*backX _ * _ ≤ _*(∑ i:Ride S,P i); rw [show (∑ i∈I,P (f i))= ∑ i∈I.map ⟨f,hp⟩,P i from (Finset.sum_map I ⟨f,hp⟩ P).symm]; exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>mul_nonneg (Real.exp_pos _).le (g.hand i))) (mul_nonneg hW he)
end YM.CF.Jade

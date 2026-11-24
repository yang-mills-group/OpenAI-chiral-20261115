import YM.CF.Muse.Text
import YM.CF.Feu.Pollen
 
 
 
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
local instance zelP_P0 :MeasurableSpace (Finset (Sat S)):= ⊤
local instance zelP_P1 :MeasurableSingletonClass (Finset (Sat S)):=⟨fun _=>trivial⟩
local instance zelP_P2 :MeasurableSpace (List (Hos S r)):= ⊤
local instance zelP_P3 :MeasurableSingletonClass (List (Hos S r)):=⟨fun _=>trivial⟩
local instance zelP_P4 :Finite ↥(Sil S r):=Set.Finite.to_subtype sill_p
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
abbrev raiseP (pp:BudgetPoint)(A:Track (Ride S) (Raid (Dwell (mid N B))))(k:ℕ): Track (Ride S) (Raid (Dwell (mid N B))):= fun O i=> composeCost pp.order (pp.order.factorial*A O i) (brim pp k (Stilo.bay O))
lemma paysV(B:BudgetPoint)(h:0≤ Aγ): 0 ≤ raiseP B Aγ k:=by intro i t; have he:1 ≤ brim B k (Stilo.bay i):= one_le_pow₀ (le_add_of_nonneg_right (by positivity)); change 0≤ composeCost ..; have hV:0 ≤ Aγ i t:= h i t; unfold Jet.composeCost; positivity
variable (Y:Support (Domain N B))(C:ℝ)(A':ℝ)(hp:Y.Nonempty)(V₀:ℝ)(o:Seat (mid N B))(hA:0≤Aγ)(hv:0 ≤ V₀)
local notation "Zr"=> raiseP pp Aγ
local notation "Zv"=> Scree.tariff pp o V₀
local notation "Υ"=> (Strung Y (rateT Zv Aγ) k)
variable (a:ℝ)(u:0<a)
include u hA hv
lemma bills(h: Strung Y (rateT (Scree.tariff pp o V₀) Aγ) k (C+a) A'): Strung Y (rateT (Scree.tariff pp o V₀) (raiseP pp Aγ k)) k C (leaps pp.order pp.power a * A'):=by
 let p:=Aγ; let Q:= Zv; let U:= rateT Q p; let P':= rateT Q (raiseP pp p k); let F:= leaps pp.order pp.power a; have hQ:= verge_l o V₀ hv pp
 have hx(i:Ride S):0 ≤ P' i:=sum_nonneg (fun j _=>mul_nonneg (hQ.fee j) (paysV _ _ hA _ _)); have he:0≤ F:=by unfold F leaps; positivity
 let Y(i:Ride S):= coverNumber k (Stilo.bay i); let v(i):=F*Real.exp (a*(Y i:ℝ))
 have ht(i:Ride S) : P' i≤ v i *U i:=by
    unfold U P' rateT joinV; rw [mul_sum]; apply sum_le_sum; intro j _; have he:= leaseT (j:=pp.order) pp.power pp Aγ i k rfl a u (Aγ i j) (hA i j) -- check ABI
    apply le_trans (mul_le_mul_of_nonneg_left he (hQ.fee j)); unfold v p Y Q; exact le_of_eq (by ring)
 refine ⟨hx,fun i g=>?_ ,?_⟩
 · exact h.spear _ (fun z=>g (le_antisymm (let H:= ht i; (H.trans_eq (show v i* U i=0 from by rw [show U i=0 from z,mul_zero]))) (hx i))) -- g expects direct not ⟂. tune
 let Uv:ℝ:=stampQ (Domain N B) k (C+a) U; apply le_trans _ (mul_le_mul_of_nonneg_left h.pay he); change (∑ i: Ride S,Trees.currency k C (Stilo.bay i)*P' i) ≤ F*∑ i:Ride S,Trees.currency k (C+a) (Stilo.bay i)*U i; rw [mul_sum]; apply sum_le_sum; intro i _; apply le_trans (mul_le_mul_of_nonneg_left (ht i) (Real.exp_pos _).le); unfold v Y Trees.currency; rw [add_mul,Real.exp_add]; exact le_of_eq (by ring)
end YM.CF.Jade

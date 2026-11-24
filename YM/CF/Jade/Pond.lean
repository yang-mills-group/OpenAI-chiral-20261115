import YM.CF.Jade.Lent
set_option autoImplicit false
set_option maxHeartbeats 850000
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
local instance pond_P0 :MeasurableSpace (Finset (Sat S)):= ⊤
local instance pond_P1 :MeasurableSingletonClass (Finset (Sat S)):=⟨fun _=>trivial⟩
local instance pond_P2 :MeasurableSpace (List (Hos S r)):= ⊤
local instance pond_P3 :MeasurableSingletonClass (List (Hos S r)):=⟨fun _=>trivial⟩
local instance pond_P4 :Finite ↥(Sil S r):=Set.Finite.to_subtype sill_p
local notation "Sν"=> (Sil S r)
local notation "ΦT"=> (tale S k t)
local notation "dP"=> Directions SU.group (Domain P B)
open Girt Plume
-- expenses at actual Fiber, input tag incidence charge single budget without losing count factor
variable {E:Type}[Fintype E] (T1:E→ ↥(Sil S r)→ ↥(tale S k t)→ Track (Ride S) (Raid (LeanV (Single (mid N B)))))
variable (F:Finset E) (z:ℝ) {ρ a c:ℝ}(hv:0<ρ)(o:Site (Domain N B))(K_:ℕ)
variable(Pz:E→ ↥(Sil S r) →Track (Ride S) ℝ)
local notation "VP"=> stake (n:=LeanV (Single (mid N B))) z
local notation "μ"=> tableG SU.group (Bond (Domain P B)) ρ
variable (hk: ∀ T':Sil S r,(∑ i ∈ F,invoiceB K_ a o (Pz i T')) ≤ c)
variable (b': ∀ (i:E)(A:Sil S r)(O:Ride S),(∫ z':Directions SU.group (Domain P B),rateT (stake z) (T1 i A (velt (S:=S) z' k t)) O ∂tableG SU.group (Bond (Domain P B)) ρ) ≤ Pz i A O)
local notation "Xc"=> (fun i R p=>∫ x:Cord S, T1 i (era x.2.2) (velt (S:=S) x.2.1.2 k t) R p ∂plummy S ρ)
include hk b' hv
lemma pay_r : (∑ i∈F,invoiceB K_ a o (rateT VP (Xc i))) ≤ c:=by
 let Y:=Sν; let Φ (i:E)(t:Ride S):=∫ z:Ids (mid P B),Pz i (era z) t∂depot _
 have pu(i:E): rateT VP (Xc i)≤ Φ i:=by
    intro t'; haveI:=plum_p S hv; have ht:= rate_m (plummy S ρ) VP (fun x:↥(Sil S r) × ↥(tale S k t)=> T1 i x.1 x.2) (fun x=>stamp x k t r) stamp_m t'; change rateT VP (Xc i) t'=(∫ x:Cord S, rateT VP (T1 i (era x.2.2) (velt x.2.1.2 k t)) t'∂plummy S ρ) at ht; rw [ht, show (∫ x:Cord S,_ ∂plummy S ρ)= (∫ A:Ids (mid P B),(∫ z':dP,rateT VP (T1 i (era A) (velt (S:=S) z' k t)) t'∂μ) ∂depot _) from (eyes (S:=S) (fun a b=> rateT VP (T1 i a b) t') hv).2]
    exact integral_mono (frill _ (sill_m (S:=S)) (fun x:Y=> ∫ z', rateT VP (T1 i x (velt (S:=S) z' k t)) t'∂μ) _) (frill _ sill_m (fun x:Y=> Pz i x t') _) (fun j=>b' i (era j) t')
 apply (sum_le_sum (fun i _=> invoice_m o _ _ (pu i))).trans; unfold Φ; simp_rw [invoiceW (depot _) _ (fun x=>era x) (sill_m (S:=S) (r:=r)) o]; rw [←MeasureTheory.integral_finsetSum]; exact (integral_mono (show Integrable _ (depot _) from frill _ sill_m (fun t:Y=> ∑ i∈F,invoiceB K_ a o (Pz i t)) _) (integrable_const c) (fun i=>hk _)).trans_eq (by simp); exact fun i _=> frill _ sill_m (fun x:Y=> invoiceB K_ a o (Pz i x)) _ -- K'_ arguments tune
end YM.CF.Jade

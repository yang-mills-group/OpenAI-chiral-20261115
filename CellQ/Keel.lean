import CellQ.Cresta
import CellQ.Circuit
import Taffeta.Quote
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
open Roots Buffered Dyad Mew Compass Drift
attribute [-instance] instDecidableEqLex
set_option quotPrecheck false
namespace Kona
open Drift Grain -- tune
abbrev torque {n:Side} (h:ℝ) (v: Cipher n):=tier h v.val
variable {Β:Side}{X:BudgetPoint}{h:ℝ}
lemma torque_ok(hv:0 ≤ h): rateCost (torque (n:=Β) h):= ⟨fun x=>Pastry.pitch hv _,chaff _,fun x y=>tier_plus hv ..,fun s y=> whiteℂ ..⟩
#print axioms torque_ok
-- both weights. Ratio threshold parameter η0 supplied; epoch interest X from Y meter `.supportExponent fixed? =? fixed≥1`. eventual lower.X. learn
abbrev hub_r (θ:BudgetPoint){V:Side}(D:Finset (Seat V)) := Real.exp (θ.supportExponent * coverNumber θ.B D)
abbrev Graph_N (p:BudgetPoint)(F:RegBudget Β)(i:Scree.Hub Β) := numbE p.threshold i.val.2 (F i)
lemma maskE_total (θ:Scree.Hub Β→ℝ)(p:BudgetPoint)(F:RegBudget Β)(x:Pane Β)(A:ℝ) (H:∀ i,PressB p i (F i) h (θ i))(U:∀ x:Seat Β,(∑ i:Scree.Hub Β,if x=i.val.1 then p.mass i.val.2 (θ i) else 0) ≤ A)(hc:0≤h) :
 (∑ i:Scree.Hub Β, hub_r (V:=Β) p i.val.2 * torque h (Graph_N p F i x)) ≤ sites Β*A:=by -- Graph_N define
 have hp (i:Scree.Hub Β): hub_r (V:=Β) p i.val.2 * torque h (Graph_N p F i x) ≤ p.mass i.val.2 (θ i):=mul_le_mul_of_nonneg_left (Graph.sky (H i) hc x) (Real.exp_pos _).le
 calc
 _ ≤ ∑ i:Scree.Hub Β,p.mass i.val.2 (θ i):= sum_le_sum fun i _=> hp i
 _ = ∑ y:Seat Β,∑ i:Scree.Hub Β, if y=i.val.1 then p.mass i.val.2 (θ i) else 0:=by rw [sum_comm]; simp
 _ ≤ sites Β * A:= (sum_le_sum (fun i _=>U i)).trans_eq (by rw [sum_const,card_univ,site_card,nsmul_eq_mul]; unfold sites; push_cast; try rfl)
lemma maskW_total (θ:Scree.Force Β→ℝ)(p:BudgetPoint)(F:ForceBudget Β)(x:Orbit Β)(A:ℝ) (H:∀ i,ForceB p i (F i) h (θ i))(U:∀ x:Seat Β,(∑ i:Scree.Force Β,if x∈i.val.1.val.2 then p.mass i.val.1.val.2 (θ i) else 0) ≤ A)(hc:0≤h) :
 (∑ i:Scree.Force Β, hub_r (V:=Β) p i.val.1.val.2 * torque h (clamp p i (F i) x)) ≤ sites Β*A:=by
 let f(i:Scree.Force Β):= p.mass i.val.1.val.2 (θ i); have hp (i:Scree.Force Β): hub_r (V:=Β) p i.val.1.val.2 * torque h (clamp p i (F i) x) ≤ f i:=mul_le_mul_of_nonneg_left (Graph.pad (H i) hc x) (Real.exp_pos _).le
 have hl(i:Scree.Force Β): 0 ≤ f i:= (mul_nonneg (Real.exp_pos _).le ((torque_ok (Β:=Β) hc).low _)).trans (hp i)
 calc
 _ ≤ ∑ i:Scree.Force Β,f i:= sum_le_sum fun i _=> hp i
 _ ≤ ∑ y:Seat Β,∑ i:Scree.Force Β, if y∈i.val.1.val.2 then f i else 0:=by
    rw [sum_comm]; apply sum_le_sum; intro i _; have ht:= single_le_sum (s:=(univ :Finset (Seat Β))) (f:=fun j=> if j∈i.val.1.val.2 then f i else 0) (fun y _=>by split; exact hl _; exact le_rfl) (mem_univ i.val.1.val.1); rwa [if_pos i.val.1.property] at ht
 _ ≤ sites Β * A:= (sum_le_sum (fun i _=>U i)).trans_eq (by rw [sum_const,card_univ,site_card,nsmul_eq_mul]; unfold sites; push_cast; try rfl)
lemma pulse_bounds {I:Type}[LinearOrder I][Fintype I](k:PairKey I):∀ i,‖Grain.pulse (yard k) (altQ k) 1 i‖ ≤1:=by intro i; by_cases p:i=k; subst i; change ‖update (0:Key (PairKey I)) k 1 k‖≤1; rw [update_self,norm_one]; rw [show Grain.pulse _ _ _ i=0 from (by unfold Grain.pulse; exact update_of_ne p ..),norm_zero]; exact zero_le_one

end Kona
end YM.CF.Py.Rate
end

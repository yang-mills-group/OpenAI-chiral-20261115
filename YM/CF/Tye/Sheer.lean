import YM.CF.Tye.Shine
import YM.CF.Lich.Spear
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Tye
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Corne Lich Lich.Muster Rink Jet Vol
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}
variable {x e m:ℝ}(A:Muster G S x e T)(M:Monk SU.group S)(s:Signed)(b:Site (Domain N B))(g:Site (Domain N B)→ SU.group.El)
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal PhysicalNext.OrderedAffine2B.SymRows Channels Locations
variable {d:ℕ}
local notation "Y"=> clue S s b M
local notation "V"=> shiftZ g M
local notation "F"=> cedar M
variable (h:K.Funds S T)(hp:FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) m)(hv:120 ≤ radiusB x)(hz:0 < m)(hA: Reef.Rare T.up)(hB:Reef.Rare T.down)(ht: LocalRatio A.vita)(hi:0 < A.rota)(hm:4*A.rota < A.vita.radius)(hb:0 < A.beta)

local notation "d"=> Domain N B
local notation "d'"=> Domain P B
local notation "L"=> Stores.till x

variable (t:Signed)(w: Palot.leaf (Site (Domain N B)))(k:ℕ) {r:ℕ}
include h hp hv hz
lemma extU_g(i:Site (Domain P B))(K:ℕ→ RG.Atom SU.group r)(P:∀ j,(K j).Invariant): extU A (shiftZ g M) t k w i (haste L K)= extU A M t k w i (haste L K):=by
 unfold Lich.Muster.extU; rw [gauge_s T x _ _ _ _ g M h hp hz hv,Work.F05.pull_gauge_zero]; unfold Lich.Muster.crop; refine tsum_congr fun j=>?_ ; split; exact lushP _ _ _ (gauge_l _ _) _ (haste_g _ i _ _ _ _ P); rfl
lemma sapU_g(i:Site (Domain P B)): sapU A (shiftZ g M) t k w i= sapU A M t k w i:=by
 unfold Lich.Muster.sapU; rw [gauge_s T x _ _ _ _ g M h hp hz hv,Work.F05.pull_gauge_zero]; unfold Lich.Muster.crop; refine tsum_congr fun j=>?_ ; split; exact path_p _ _ _ _ (gauge_l _ _) _ (rod_g _ i _ _ _ _); rfl
lemma extV_g(i:Site (Domain N B))(K:ℕ→ RG.Atom SU.group r)(P:∀ j,(K j).Invariant): extV A (shiftZ g M) t k w i (haste (L/S.patch.L.val) K)= extV A M t k w i (haste (L/S.patch.L.val) K):=by
 unfold Lich.Muster.extV; rw [show (shiftZ g M).V=(Lattice.gauge _ _) from rfl,Work.F05.pull_gauge_zero]; unfold Lich.Muster.crop; refine tsum_congr fun j=>?_ ; split; exact peerP _ _ _ (gauge_l _ _) _ (haste_g _ i _ _ _ _ P); rfl
lemma extVb_g(i:Site (Domain N B))(K:ℕ→ RG.Atom SU.group r)(P:∀ j,(K j).Invariant): extV A (shiftZ g M) t k w i (batch K (L/S.patch.L.val))= extV A M t k w i (batch K (L/S.patch.L.val)):=by
 unfold Lich.Muster.extV; rw [show (shiftZ g M).V=(Lattice.gauge _ _) from rfl,Work.F05.pull_gauge_zero]; unfold Lich.Muster.crop; refine tsum_congr fun j=>?_ ; split; exact peerP _ _ _ (gauge_l _ _) _ (batch_g _ i _ _ _ _ P); rfl
lemma sapC_g(i:Site (Domain N B)): sapC A (shiftZ g M) t k w i= sapC A M t k w i:=by
 unfold Lich.Muster.sapC; rw [show (shiftZ g M).V=(Lattice.gauge _ _) from rfl,Work.F05.pull_gauge_zero]; unfold Lich.Muster.crop; refine tsum_congr fun j=>?_ ; split; exact path_p _ _ _ _ (gauge_l _ _) _ (rod_g _ i _ _ _ _); rfl
lemma shard_g: shardy A (shiftZ g M) k w=shardy A M k w:=by
 obtain ⟨a,b',H,Z'⟩:=h.feeds; unfold shardy; apply congrArg Neg.neg; apply congrArg averaged; ext t; refine congrArg₂ (·-·) (sum_congr rfl fun i _=>?_) (sum_congr rfl fun i _=>?_)
 · unfold Lich.Muster.river; rw [sapU_g A M g h hp hv hz t,extU_g A M g h hp hv hz t w k i _ (fun j=>( H.invariant  j).2.1),extU_g A M g h hp hv hz t w k i _ (fun j=>( H.invariant  j).2.2),extU_g A M g h hp hv hz t w k i _ (fun j=>( H.invariant  j).1)]
 unfold Lich.Muster.flows; rw [sapC_g A M g h hp hv hz t,extV_g A M g h hp hv hz t w k i _ (fun j=>(Z'.invariant j).2.1),extV_g A M g h hp hv hz t w k i _ (fun j=>(Z'.invariant j).2.2),extV_g A M g h hp hv hz t w k i _ (fun j=>(Z'.invariant j).1),extVb_g A M g h hp hv hz t w k i _ (fun j=>(Z'.invariant j).2.1),extVb_g A M g h hp hv hz t w k i _ (fun j=>(Z'.invariant j).2.2)]
include hA hB
lemma extU_f(i:Site (Domain P B))(K:ℕ→ RG.Atom SU.group r)(P:∀ j,Reef.Prist (K j)): extU A (Rink.cedar M) t k w i (haste L K)= extU A M t k w i (haste L K):=by
 unfold Lich.Muster.extU; rw [echo_s T x _ _ _ _ M h hp hz hv hA,Reef.echo_p]; unfold Lich.Muster.crop; refine tsum_congr fun j=>?_ ; split; exact lushP _ _ _ (mint_b _) _ (haste_f _ i _ _ _ P); rfl
lemma sapU_f(i:Site (Domain P B)): sapU A (Rink.cedar M) t k w i= sapU A M t k w i:=by
 unfold Lich.Muster.sapU; rw [echo_s T x _ _ _ _ M h hp hz hv hA,Reef.echo_p]; unfold Lich.Muster.crop; refine tsum_congr fun j=>?_ ; split; exact path_p _ _ _ _ (mint_b _) _ (rod_f _ i _ _ _); rfl
lemma extV_f(i:Site (Domain N B))(K:ℕ→ RG.Atom SU.group r)(P:∀ j,Reef.Prist (K j)): extV A (Rink.cedar M) t k w i (haste (L/S.patch.L.val) K)= extV A M t k w i (haste (L/S.patch.L.val) K):=by
 unfold Lich.Muster.extV; rw [show (Rink.cedar M).V=(Reef.echo _) from rfl,Reef.echo_p]; unfold Lich.Muster.crop; refine tsum_congr fun j=>?_ ; split; exact peerP _ _ _ (mint_b _) _ (haste_f _ i _ _ _ P); rfl
lemma extVb_f(i:Site (Domain N B))(K:ℕ→ RG.Atom SU.group r)(P:∀ j,Reef.Prist (K j)): extV A (Rink.cedar M) t k w i (batch K (L/S.patch.L.val))= extV A M t k w i (batch K (L/S.patch.L.val)):=by
 unfold Lich.Muster.extV; rw [show (Rink.cedar M).V=(Reef.echo _) from rfl,Reef.echo_p]; unfold Lich.Muster.crop; refine tsum_congr fun j=>?_ ; split; exact peerP _ _ _ (mint_b _) _ (batch_f _ i _ _ _ P); rfl
lemma sapC_f(i:Site (Domain N B)): sapC A (Rink.cedar M) t k w i= sapC A M t k w i:=by
 unfold Lich.Muster.sapC; rw [show (Rink.cedar M).V=(Reef.echo _) from rfl,Reef.echo_p]; unfold Lich.Muster.crop; refine tsum_congr fun j=>?_ ; split; exact path_p _ _ _ _ (mint_b _) _ (rod_f _ i _ _ _); rfl
lemma shard_f: shardy A (Rink.cedar M) k w=shardy A M k w:=by
 obtain ⟨a,b',H,Z'⟩:=h.feeds; unfold shardy; apply congrArg Neg.neg; apply congrArg averaged; ext t; refine congrArg₂ (·-·) (sum_congr rfl fun i _=>?_) (sum_congr rfl fun i _=>?_)
 · unfold Lich.Muster.river; rw [sapU_f A M h hp hv hz hA hB t,extU_f A M h hp hv hz hA hB t w k i _ (fun j=>(hA j).2.1),extU_f A M h hp hv hz hA hB t w k i _ (fun j=>(hA j).2.2),extU_f A M h hp hv hz hA hB t w k i _ (fun j=>(hA j).1)]
 unfold Lich.Muster.flows; rw [sapC_f A M h hp hv hz hA hB t,extV_f A M h hp hv hz hA hB t w k i _ (fun j=>(hB j).2.1),extV_f A M h hp hv hz hA hB t w k i _ (fun j=>(hB j).2.2),extV_f A M h hp hv hz hA hB t w k i _ (fun j=>(hB j).1),extVb_f A M h hp hv hz hA hB t w k i _ (fun j=>(hB j).2.1),extVb_f A M h hp hv hz hA hB t w k i _ (fun j=>(hB j).2.2)]
end YM.CF.Tye

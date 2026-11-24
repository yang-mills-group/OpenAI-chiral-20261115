import YM.CF.Pso.Solo
import YM.CF.Vp929.Canon.Knit
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Beau
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k' m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
open Ione
local notation "N"=> P.order
local notation "Xo"=>Skye.Seat n
open Ione Larch
open Taxi Geo RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
local notation "Hz"=> Scree.Hub n
open Trees
open Salt
open Push.BetaTransport Reef
variable(P:BudgetPoint)(R:PathData SU.group){q:Clip}{σ C Λ:ℝ}(p:R.Bounds q σ C Λ)(A Γ:ℝ)(D': DayT P.order Γ)(DA: OriK P.order A)(hc:0≤Γ)(ha:0≤ A)(hw:Decent q P)(hp:Geo.Width P q σ)(hn:60 <(More n).val)
local notation "Rd"=> (P.supportExponent+1+1)
variable (T:Ids n)(hv:1 ≤ h)(hL:(P.supportExponent+1+1)/(P.B:ℝ)≤σ/8)(h6:6 ≤ P.B)(r: Rare R) (E: RegBudget n)(sL:ℕ)(p0:IncX Utrue E P h x)
local notation "T'"=> caw P sL E
local notation "T0"=>can_V P sL E
local notation "u'"=> lureC (realH T')
local notation "ER"=> Coil T' + lite_b n P R q u'+ lit_P n P R q u'
local notation "Ω"=>voids T'- ΘK T P R q u'
local notation "γ"=> rate_μ P q σ C Γ u'
local notation "uL"=>belt_K P sL Γ*x+ γ
local notation "Rb"=> rate_b P q σ C A u'
local notation "Rh"=> rate_h P q σ C A u'
local notation "ε"=>fee_l P Γ*x+Rb+Rh
-- Auth log pressure.Theorem bend Φ all.X poles.AMB. full A=abs.Bl.No losses. verify.Lane.
local notation "Eh"=> (T0+writ_E ER)
local notation "dQ"=> (writ_K Ω)
local notation "Ts"=> Sweep n
local notation "Up"=> (uL+tray_H P.order * uL)
open Iva Lilt
lemma polarHeadPlus (E F : RegBudget n) : head_L (E+F)=head_L E+head_L F :=
 funext fun _=>funext fun _=>map_add cut_V _ _
lemma headDouble : head_L (head_L E)=head_L E := by
  have he:=polarHeadPlus (cry_H E) (head_L E)
  rw [bareH, show head_L (cry_H E)=0 from poolZ E, zero_add] at he
  exact he.symm

include p DA ha hw hp hn hv
lemma brol_head : head_L (brol P R q sL E)=head_L E:=by
 let Tη:= caw P sL (cry_H E); let Qb:=can_V P sL (cry_H E); let d:=lureC (realH Tη);
 have ht: Silent Tη:=by funext i V; change cut_V (Tη i V) =0; unfold Tη caw; split; exact sass (poolZ E) _ _; exact map_zero _
 have hq: Silent Qb:=by funext i V; change cut_V (Qb i V)=0; unfold Qb can_V; split; exact map_zero _; exact sass (poolZ E) _ _
 let Op:= Qb+writ_E (Coil Tη+lite_b n P R q d+lit_P n P R q d); have hA: Silent Op:= sail_g _ _ hq (light_F _ (sail_g _ _ (sail_g _ _ (sail_F0 Tη ht) (thirst P R p A d DA ha hw hp hn hv sL).2.2.1) (crown_V P R p A d DA ha hw hp hn hv sL).2.2.1))
 change head_L (Op+head_L E)=head_L E
 rw [polarHeadPlus, show head_L Op=0 from hA,zero_add,headDouble]
end YM.CF.Beau

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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Taxi RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
namespace Test
-- Transfer averaging. Specialized budgets. Degree 0 and 2.
set_option quotPrecheck false
open Cycle929 Larch Bake Salt Trees Push.BetaTransport
variable {n:Side}{L:ℕ}{Q:BudgetPoint}{A h a c d v α σ C Λ k β j w:ℝ}
local notation "D'"=> RegBudget n
local notation "Hz"=> Scree.Hub n
variable {X Y:RegBudget n}{Z W:Cusp n}{R:PathData SU.group}{b:Clip}
local notation "ζ"=> Cash.prominence Q

open TestW
/-- Uniformly bounded in cover-number (integer units of the budget at this height). -/
def coverEnd (B M:ℕ) (X:RegBudget n):Prop:=
  ∀ i:Scree.Hub n, M < coverNumber B i.val.2 → X i=0

lemma coverEndWrite (B M:ℕ) (X:RegBudget n) (t:coverEnd B M X) : coverEnd B M (writ_E X) := by
  intro i h
  funext v
  unfold writ_E
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply]
  rw [Finset.sum_eq_zero, smul_zero]
  intro s _
  change (suit_Y s⁻¹ (X (moveHub s i) _))=0
  rw [t]
  · exact map_zero _
  rw [show coverNumber B (moveHub s i).val.2=_ from glow_q s B i.val.2]; exact h

lemma NetXCover {F:Scree.Hub n→ Scree.Hub n}(p:Extension L Q n F) :
   coverEnd Q.B (max (mstar L) 1) (NetX F Q X):=by
 let R:=max (mstar L) 1; let X':= rightS Q X
 have hu (i:Scree.Hub n)(t:1<coverNumber Q.B i.val.2): X' i=0:= by unfold X' rightS; rw [if_neg (fun (p:i ∈ massH Q)=>t.not_ge (mem_filter.mp p).2)]
 have hv:coverEnd Q.B R (warp_E F X'):=by
    intro i v; unfold warp_E sunY
    apply sum_eq_zero; intro j w; apply hu
    have hv:(mstar L) < coverNumber Q.B (F j).val.2 ∧
        1 < coverNumber Q.B (F j).val.2 := by
      rw [(mem_filter.mp w).2]; exact ⟨(le_max_left ..).trans_lt v,(le_max_right ..).trans_lt v⟩
    by_cases h:shortHub Q L j
    · exact False.elim (ne_of_gt hv.1 (p.cap _ h))
    rw [p.held j h] at hv; exact hv.2
 intro i p
 change X' i - (writ_E (warp_E F X')) i=0
 rw [coverEndWrite _ _ _ hv _ p,hu i ((le_max_right ..).trans_lt p),sub_self]

end Test
end YM.CF.Py.Rate

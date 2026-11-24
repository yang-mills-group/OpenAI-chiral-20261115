import YM.CF.Pso.Solo
import Gingham.Linen.Tatting
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

open Linen
lemma frost_cut (u:Cipher n):minusO u=cut_V u:=by
 apply pimp_Q
 intro i; change _=crumb (blind_E _).val i
 rw [Linen.surf,shelter_Q]; simp only [card_eq_zero]

lemma Silent.icing {X:Scree.Hub n}(s:Silent E)(u:Pane n):
 minusO (E X u)=0:=by rw [frost_cut, sass s]
lemma Silent.zaffre (s:Silent E)(k:ℕ) : Zaffre E P k :=
 fun i _=>funext fun u=>Silent.icing E s u

lemma still_pool (H:ℕ→Scree.Hub n)(F:ℕ→InkD n)
    (f: ∀ i v,cut_V (F i v)=0): Silent (pool_F H F P):=by
 funext X v
 change cut_V (pool_F H F P X v)=0
 unfold pool_F caj lasting zenS
 split; swap
 · exact map_zero cut_V
 let x:= fun i:ℕ=> (sZ H F X i v)
 change cut_V (∑' j,x j) = _
 by_cases t:Summable x; swap
 · rw [tsum_eq_zero_of_not_summable t,map_zero]
 have g j:cut_V (x j)=0:=by unfold x sZ;split;exact f j v; exact map_zero cut_V
 exact (cut_V.hasSum t.hasSum).unique (by simp only [g]; exact hasSum_zero)


lemma muteM (v:ℝ) : cut_V (moldV n v)=0:= by
 rw [←frost_cut]
 exact minusO_crown v (by change v • (1:FC _) = _; rw [Complex.coe_smul])
lemma paler (d:ℝ): Silent (lite_b n P R q d):=by apply still_pool; intro i v; exact muteM _
lemma paler_s (d:ℝ): Silent (lit_P n P R q d):=by apply still_pool; intro i v; exact muteM _

/-- brol changes zero positive-degree; assertion even off-support/off lights -/
lemma brol_frost : frosting (brol P R q sL E)=frosting E:=by
 let Tη:= caw P sL (cry_H E); let Qb:=can_V P sL (cry_H E); let d:=lureC (realH Tη);
 have ht: Silent Tη:=by funext i V; change cut_V (Tη i V) =0; unfold Tη caw; split; exact sass (poolZ E) _ _; exact map_zero _
 have hq: Silent Qb:=by funext i V; change cut_V (Qb i V)=0; unfold Qb can_V; split; exact map_zero _; exact sass (poolZ E) _ _
 let Op:= Qb+writ_E (Coil Tη+lite_b n P R q d+lit_P n P R q d)
 have hA: Silent Op:= sail_g _ _ hq (light_F _ (sail_g _ _ (sail_g _ _ (sail_F0 Tη ht) (paler P R d)) (paler_s P R d)))

 funext i v
 change minusO ((Op+head_L E) i v)=_
 have k:=congrArg (fun F:RegBudget n=>minusO (F i v)) (bareH E)
 refine Eq.trans ?_ k
 change minusO (Op i v+head_L E i v)=minusO (cry_H E i v+head_L E i v)
 rw [minusO_add, (Silent.icing Op hA),minusO_add,(Silent.icing _ (poolZ E))]
#print axioms brol_frost


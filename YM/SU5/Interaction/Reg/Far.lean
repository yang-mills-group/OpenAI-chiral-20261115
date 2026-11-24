import YM.SU5.Interaction.Reg.High
import YM.CF.Vp929.Stage.Bolts

/-! Tail localizations in the unmarked transport. Use α_Ub proof to check brol and cf. makeGauge proof. -/
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
include p DA ha hw hp hn hv
lemma brolExact : head_L (brol P R q sL E)=head_L E:=by
 let Tη:= caw P sL (cry_H E); let Qb:=can_V P sL (cry_H E); let d:=lureC (realH Tη)
 have ht: Silent Tη:=by funext i V; change cut_V (Tη i V) =0; unfold Tη caw; split; exact sass (poolZ E) _ _; exact map_zero _
 have hq: Silent Qb:=by funext i V; change cut_V (Qb i V)=0; unfold Qb can_V; split; exact map_zero _; exact sass (poolZ E) _ _
 let Op:= Qb+writ_E (Coil Tη+lite_b n P R q d+lit_P n P R q d); have hA: Silent Op:= sail_g _ _ hq (light_F _ (sail_g _ _ (sail_g _ _ (sail_F0 Tη ht) (thirst P R p A d DA ha hw hp hn hv sL).2.2.1) (crown_V P R p A d DA ha hw hp hn hv sL).2.2.1))
 funext i V
 change cut_V (Op i V + head_L E i V)=cut_V (E i V)
 rw [map_add,sass hA,zero_add]
 apply Eq.symm; conv_lhs => arg 2; rw [show E i V = cry_H E i V + head_L E i V from congrFun (congrFun (bareH E).symm i) V]
 rw [map_add,sass (poolZ E),zero_add]
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
set_option quotPrecheck false
open Cycle929 Larch Bake Salt Trees Push.BetaTransport
open AnalyticBridge.VerifiedReset.Collection
variable {n:Side}{L:ℕ}{Q:BudgetPoint}{A h a c d v α σ C Λ β j w:ℝ}
local notation "D'"=> RegBudget n
local notation "V'"=> Skye.Seat n
local notation "Gξ"=> SU.group
local notation "Px"=> Lattice.PlaqAxes
local notation "φ"=> AnalyticBridge.VerifiedReset.petals
local notation "H_"=> AnalyticBridge.VerifiedReset.heads
local notation "Z_"=> AnalyticBridge.VerifiedReset.counter
local notation "Lρ"=> Cash.prominence Q
variable {R:PathData SU.group}{b:Clip}(u:Cease Q R b α v σ C Λ n) (T:Ids n) (g:1 ≤ h)
local notation "Fr"=> c
local notation "Θ_"=> ΘK T Q R b (-1)
local notation "ℓ1"=> (lite_b n Q R b (-1))
local notation "ℓ2"=> (lit_P n Q R b (-1))
local notation "μr"=> (rate_b Q b σ C α (-1))
local notation "μp"=> (rate_h Q b σ C α (-1))
local notation "Λr"=> (rate_μ Q b σ C v (-1))
local notation "Kp"=> Push.BetaTransport.kinetic
namespace QuiltB
variable {F:Scree.Hub n→ Scree.Hub n}(p:Extension L Q n F)
local notation "CR"=> creditR Q R b n
local notation "CT"=> creditT Q R b T
include u g T
lemma packScalar : GSingle (packR Q R b F):= light_F _ (scalar_warp (creditTune u T g).2.2.1)
end QuiltB

section truncation
open TestW
abbrev OnlyHere (Q:BudgetPoint)(K:ℕ)(F:RegBudget n) := ∀ i:Scree.Hub n,K< coverNumber Q.B i.val.2 → F i=0
lemma OnlyHere.writ {F:RegBudget n}{K:ℕ}(t:OnlyHere Q K F): OnlyHere Q K (writ_E F) := by
 intro i r; funext x; unfold writ_E; simp only [Pi.smul_apply, Finset.sum_apply]; change plight_C n • (∑ j:Sweep n,suit_Y j⁻¹ _) = (0:Cipher n); rw [sum_eq_zero,smul_zero]
 intro j _; have h: F (moveHub j i)=0:= t _ (by rw [show coverNumber _ (moveHub j i).val.2 =_ from glow_q j Q.B i.val.2]; exact r); rw [h]; exact map_zero _
lemma OnlyHere.sub {F G: RegBudget n}{K:ℕ}(f:OnlyHere Q K F)(g:OnlyHere Q K G):OnlyHere Q K (F-G):= fun i v=>by rw [Pi.sub_apply,f i v,g i v,sub_self]
lemma OnlyHere.larger {F:RegBudget n}{K S:ℕ}(p: K≤S)(h:OnlyHere Q K F):OnlyHere Q S F:=fun i v=> h i (p.trans_lt v)
lemma OnlyHere.warp {f:Scree.Hub n→ Scree.Hub n}(p:Extension L Q n f){F:RegBudget n}{K:ℕ}(h:mstar L ≤ K)(t:OnlyHere Q K F): OnlyHere Q K (warp_E f F) := by
 intro i v; apply sum_eq_zero; intro j u; have o: f j=i:=(mem_filter.mp u).2
 by_cases q:shortHub Q L j
 · rw [←o,p.cap _ q] at v; exact (h.not_gt v).elim
 rw [p.held _ q] at o; rw [o]; exact t i v
lemma shaves (v:RegBudget n):OnlyHere Q 1 (shaveL Q v):= by
 intro i x; change (if i∈massH Q then _ else _)= (0:InkD n); exact if_neg (fun (q : i∈ massH Q)=> x.not_ge (mem_filter.mp q).2)
lemma NetHere {f:Scree.Hub n→ Scree.Hub n}(p:Extension L Q n f)(v:RegBudget n):OnlyHere Q (max 1 (mstar L)) (NetX f Q v):=by
 have ht:OnlyHere Q (max 1 (mstar L)) (shaveL Q v):=OnlyHere.larger (le_max_left ..) (shaves v)
 exact ht.sub (ht.warp p (le_max_right ..)).writ
end truncation
end Test
end YM.CF.Py.Rate

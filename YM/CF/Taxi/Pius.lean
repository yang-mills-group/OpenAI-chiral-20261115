import YM.CF.Taxi.Sheep
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Taxi
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
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
-- transfer identity Layer.I only. no analytic recurrence assumed. in-place K-F.Tx projection units at Force labels. Meas.I.Bl shift.Check. growth.Stove.Resource. stencil moment. θ CONTACTS.
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup Vow
open Geo Trees Rue Collection
local notation "Gp"=> SU.group
variable {Γ:ℝ} (P:BudgetPoint){q:Clip}(R: PathData SU.group) (x: Site (More n))
abbrev Lane(n:Side):=AnalyticBridge.VerifiedReset.Seat (More n) × AnalyticBridge.VerifiedReset.Low
abbrev χx (P:BudgetPoint)(R:PathData SU.group)(x:Lane n): Aura n:= ⟨x.1.spread (x.2.home R P 0),⟨x.1.2,(x.1.reg (x.2.home R P 0) (x.2.small_home ..)).anchor⟩⟩ -- sint
variable {σ C Λ:ℝ}(p:R.Bounds q σ C Λ)(U:Orbit n)(T: Ids n)(hc:0 ≤ Γ)(hp:DayT P.order Γ)(hw:Decent q P)(ht:Geo.Width P q σ)
local notation "M"=>More n
local notation "Ω"=> flags P.threshold U.1
abbrev regV (P: BudgetPoint)(R:PathData SU.group)(q:Clip)(d:ℝ)(x:Lane n):Cusp n := chasmR (χx P R x) (fun u:Support (More n)=> (AnalyticBridge.VerifiedReset.factor*d) • oV (herV T R q P x.1 x.2 u))
def moldV(n:Side):ℝ→L[ℝ] Cipher n:= (ContinuousLinearMap.id ℝ ℝ).smulRight (1:Cipher n)
lemma mon_v(n:Side)(v:ℝ): moldV n v=hollow (↑v):=by apply Subtype.ext; change v • 1=(↑v:ℂ) • (1:FC (Dwell n)); exact (Complex.coe_smul ..).symm
include hc hp hw
lemma lien (x: Lane n)(a:ℝ): fuelV P (regV T P R q a x) U= moldV n (stack (fun i:Low=>i.loan R q 0 P 0 a) U.1 x):=by
 rcases x with ⟨i,b⟩; let Y:= b.home R P (0:Site (More n)); let H:=AnalyticBridge.VerifiedReset.Seat.spread i Y; let F:=Y \ ∅; let G:AnalyticBridge.VerifiedReset.Seat (More n):= i; let L:=AnalyticBridge.VerifiedReset.Seat.view i U.1; have hp':Ω= (flags P.threshold L).map (αX i).toEmbedding:= by
    rw [map_eq_image]; exact (Work.H03.flags_send ..).symm -- tune
 let D:= Ω ∩ H; unfold regV; rw [shade_t]; split
 next h=>
    have hs: D.Nonempty:= Finset.not_disjoint_iff_nonempty_inter.mp (fun g=>h g.symm)
    let K' := flags P.threshold L∩ Y; have hx:D.map (αX i).symm.toEmbedding=K':=by
       have ht:D=K'.map (αX i).toEmbedding:=by unfold D; rw [show H= Y.map (αX i).toEmbedding from seats ..]; simp only [K',D, hp', Finset.map_inter]; -- tune unfold
       rw [ht]; ext; simp
    change (AnalyticBridge.VerifiedReset.factor*a) • loanW R q P 0 b (D.map (αX i).symm.toEmbedding) (L,T) = moldV n (AnalyticBridge.VerifiedReset.factor*Low.loan R q b 0 P 0 a L)
    rw [hx,mul_smul,show a • loanW R q P (0:Site (More n)) b K' (L,T)= Pastry.hollow ((↑(Low.loan R q b 0 P 0 a L):ℂ)) from pulp_w R (n:=n) 0 L b Γ hp hc hw a rfl (show K'.Nonempty from hx ▸ Finset.map_nonempty.mpr hs) T,← mon_v]; exact (map_smul (moldV n) AnalyticBridge.VerifiedReset.factor (Low.loan R q b (0:Site (More n)) P 0 a L)).symm
 next h=>
    change _= moldV n (AnalyticBridge.VerifiedReset.factor* Low.loan R q b (0:Site (More n)) P 0 a L); have ht:Healthy P.threshold Y L:=(AnalyticBridge.VerifiedReset.Seat.healthy i (G:=SU.group) P.threshold Y U.1).1 ?_; rw [Low.loan,if_pos ht,mul_zero,map_zero]; exact not_not.mp h -- tune subgoals
include ht p
lemma toast (a:ℝ) : HasSum (fun x:Lane n=> fuelV P (regV T P R q a x) U) (moldV n (layer (fun i:Low=> i.loan R q 0 P 0 a) U.1)):=by
 simp_rw [lien P R U T hc hp hw]; apply (moldV n).hasSum; rw [layer_total _ U.1 (loan_sum p ht hw 0 a)]; exact (stack_series _ _ (loan_sum p ht hw 0 a)).hasSum -- tune order
omit p ht
lemma giftD(x:Lane n)(a:ℝ)(D:Support (More n))(h':0 ≤ h): Medal P (χx P R x).val D (regV T P R q a x (χx P R x) D) h (|a| *bill_l R x.2 q Γ P):=by
 unfold regV chasmR; rw [Pi.single_eq_same]; let G:=vein_f R x.1 x.2 T Γ hp hc hw (Y:=D) (h:=h); apply (G.rum _).big; rw [Real.norm_eq_abs, abs_mul, abs_of_pos factor_pos]; exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) factor_le) (G.wage h')
end YM.CF.Taxi

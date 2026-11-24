import YM.CF.Taxi.Fine
import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Local
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
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open AnalyticBridge.VerifiedReset Push.Local Next.Foundations
variable (X0: Scree.Hub n)(o:Site (More n)){F:Pane n→ℝ}
local notation "Xp"=> X0.val.2
local notation "Op"=> X0.val.1
local notation "Z"=> villa X0
open PhysicalNext.JointLoad Heir
variable (h':BandS P X0 F c)
-- spend sheet.V FOR EACH output seat, unscaled at P threshold exactly. preserve when centering.B.Full p.Support even enlarged. constants before L
abbrev pointsF (k:BudgetPoint)(v:ℝ)(o':Skye.Seat n):ℝ:= (2:ℝ)⁻¹*((Fintype.card PlaqAxes:ℝ)*((Fintype.card PlaqAxes:ℝ)*(v*pairBill SU.group k)))
abbrev tollV (P:BudgetPoint)(V:ℝ):= (2:ℝ)⁻¹*((Fintype.card PlaqAxes:ℝ)*((Fintype.card PlaqAxes:ℝ)*(V*pairBill SU.group P)))
def priceV (P:BudgetPoint)(G:ℝ) : ℝ:=(5:ℝ)^(P.power*P.order)* (G*tollV P 1)
abbrev DayT (k:ℕ)(Q:ℝ):Prop:=∀ (n:Side)(P:BudgetPoint)(tZ:Config SU.group (More n)→Prop)(z:Skye.Seat n)(A:ℝ)(F:Config SU.group (More n)→ℝ), AnalyticBridge.VerifiedReset.Bill P z tZ A F → P.order=k→∀ i,tZ i → Signs P z (F ∘ RG.increment i) (Q*A)
variable(hQ:0 ≤ a)(t:DayT P.order a)
private lemma healV(u:motto Op o ≠0):P.Regular Z (fuelC X0 F o):=by
 let W:= counter (fluxP X0 F) o (G:=SU.group); let I:=counter_regular (G:=SU.group) o (fluxP X0 F) P; let Λ:=halo 2 {o}; exact reg_larger (AnalyticBridge.CouplingShape.reg_scale _ I) (shipT X0 o u) -- tune ns differs
lemma holdS :P.Regular Z (fuelC X0 F o):=by
 by_cases u:motto Op o=0; · unfold fuelC; rw [u,zero_smul]; exact reg_const 0
 exact healV _ _ u
include h'
private lemma cost_p : AnalyticBridge.VerifiedReset.Bill P o (Healthy P.threshold {o}) (tollV P c) (counter (G:=SU.group) (fluxP X0 F) o):=by
 apply AnalyticBridge.VerifiedReset.Bill.le (counter_bill (G:=SU.group) o (fluxP X0 F) P); unfold tollV; refine mul_le_mul_of_nonneg_left ?_ (by norm_num); let K:=c*pairBill SU.group P
 have hk:∑ i:PlaqAxes,∑ j:PlaqAxes,K=(Fintype.card PlaqAxes:ℝ)*((Fintype.card PlaqAxes:ℝ)*K):=by simp
 refine (sum_le_sum fun i _=>sum_le_sum fun j _=>?_).trans hk.le
 rw [mul_comm (pairBill SU.group P),← mul_assoc,mul_comm |fluxP X0 F _ _|]; exact mul_le_mul_of_nonneg_right (payC X0 h' _ _) (pair_nonneg ..)
include t hQ
lemma turnC(V:Pane n)(u:pingS P.threshold Z V): Signs P Op ((fuelC X0 F o) ∘ increment V) (motto Op o*(priceV P a*c)):=by
 let C:= counter (fluxP X0 F) o (G:=SU.group); let G:=stateT X0; by_cases w:motto Op o=0; · rw [fuelC,w,zero_smul,zero_mul]; exact Prism.hail norm_zero.le
 have hK: Healthy P.threshold {o} V:= Finset.disjoint_of_subset_left ((halo_subset 2 _).trans (shipT X0 o w)) (ping_le u)
 have hx:Signs P o (C ∘ increment V) (a*tollV P c):=t _ _ _ _ _ _ (cost_p X0 o h') rfl V hK
 have hw: spine P.power o Op ≤ 5^P.power:=by
    have he:= (separation_comm ..).trans_le (motors Op o w); unfold spine; refine pow_le_pow_left₀ (by positivity) ?_ P.power; have hx: (separation o Op:ℝ) ≤4:=by exact_mod_cast he
    linarith
 have hu': (5:ℝ)^(P.power*P.order)*(a*tollV P c)=priceV P a*c:=by unfold priceV tollV; ring
 have hz: Signs P Op (C ∘ increment V) (priceV P a*c):=by
    rw [←hu']; refine ⟨mul_nonneg (by positivity) hx.grade,hx.paid,fun i f y m=>?_⟩; exact (Siete.rise_i i (hx.token i f) y m).trans (mul_le_mul_of_nonneg_right ((pow_le_pow_right₀ (spine_one ..) f).trans ((pow_le_pow_left₀ (spine_pos ..).le hw _).trans_eq (pow_mul ..).symm)) hx.grade)
 have hy:= (Prism.skin hz).smul (motto Op o); rw [abs_of_nonneg (mot_l ..)] at hy; exact Prism.skills hy
lemma pension (V:Pane n)(u:pingS P.threshold Z V): Signs P Op (payout X0 F ∘ increment V) (priceV P a*c) :=by
 have he:= Prism.haloI (S:= univ (α:=Site (More n))) (fun i _=> turnC X0 i h' hQ t V u); rw [← sum_mul,mot_b,one_mul] at he; refine Prism.mint he ?_; apply Eventually.of_forall; intro i; simp [payout] -- tune
omit hQ t h'
private lemma adds {F H:Pane n→ℝ}(p:P.Regular Z F)(u:P.Regular Z H):P.Regular Z (F+H):=by
 rw [←sub_neg_eq_add,←zero_sub (_:Pane n→ℝ)]; exact reg_sub p (reg_sub (reg_const _) u)
lemma rent(x:Finset (Site (More n))) : P.Regular Z (∑ i∈x,fuelC X0 F i):=by induction x using Finset.induction_on with| empty=> rw [sum_empty]; exact reg_const _|insert i s k ih=> rw [sum_insert k]; exact adds X0 (holdS X0 i) ih
include h' hQ t
lemma pigment : BandS P (stateT X0) (payout X0 F) (priceV P a*c):=⟨rent X0 _,fun i p=>pension X0 h' hQ t i p⟩
end YM.CF.Taxi

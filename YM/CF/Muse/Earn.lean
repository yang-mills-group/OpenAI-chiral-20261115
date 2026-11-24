import YM.CF.Muse.Text
import YM.CF.Muse.Bill
import YM.CF.Jade.Pond
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
local instance earnP_P0 :MeasurableSpace (Finset (Sat S)):= ⊤
local instance earnP_P1 :MeasurableSingletonClass (Finset (Sat S)):=⟨fun _=>trivial⟩
local instance earnP_P2 :MeasurableSpace (List (Hos S r)):= ⊤
local instance earnP_P3 :MeasurableSingletonClass (List (Hos S r)):=⟨fun _=>trivial⟩
local instance earnP_P4 :Finite ↥(Sil S r):=Set.Finite.to_subtype sill_p
local notation "Sν"=> (Sil S r)
local notation "ΦT"=> (tale S k t)
local notation "dP"=> Directions SU.group (Domain P B)
open Girt Plume
open Lilt Feu Nor
open Nor
local notation "Kκ"=> pp
local notation "vQ"=> (radiusB x)
variable (F₁:Support (Domain N B))(u ρ:ℝ)(Uq:Track (Ride S) ℝ)(Yp: Sil S r→tale S k t→Track (Ride S) (Raid (Dwell (mid N B))))(A0:Sil S r→ Track (Ride S) ℝ)(Yl:Palot.leaf (Site (Domain N B)))
local notation "pQ"=> ↥(Robe S ρ)
local notation "U₄"=> tour (S:=S) ρ
local notation "XQ"=> text_r S F₁ u ρ
local notation "Tp"=> Stilo.beamH Yl.val
local notation "rZ"=> Raid (Dwell (mid N B))
-- NO depend on outer.SC.
abbrev earnX(x t:ℝ)(k:ℕ)(Yp: Sil S r→tale S k t→Track (Ride S) (Raid (Dwell (mid N B))))(Yl:Palot.leaf (Site (Domain N B))):Raid (Dwell (mid N B)):=fun i=> ∫ a:pQ,(XQ).indicator (fun y=>(Nor.linkY pp Yl.val (Yp (era y.val.2.2) (velt y.val.2.1.2 k t) (Stilo.beamH Yl.val)) (radiusB x)) i) a∂U₄ -- tune notation expansion (XQ).indicator
variable (o:Site (Domain N B))(ho:o∈Yl.val)
variable (θ:ℝ)(hv₀:0≤θ)(z:0 ≤ Yp)(pay:∀ i j,rateT (stake θ) (Yp i j)≤ A0 i) (a:ℝ)(hp:0<a)(hρ:0 < ρ)(hk:pp.B=radiusB x)(K₄:ℝ)(hx:(tour (S:=S) ρ).real (text_r S F₁ u ρ) ≤ coverNumber (radiusB x) Yl.val * K₄)
local notation "Tμ"=> ((U₄).real (XQ))
local notation "vV"=> Scree.tariff pp o θ
local notation "Cx"=> (coverNumber (radiusB x) Yl.val:ℝ)
local notation "Cζ"=> currency (radiusB x) (pp.supportExponent + a) Yl.val
local notation "Zr"=> (reserveT pp.power pp.order (radiusB x) a)
variable (p:A0=A0)
abbrev backX (a:ℝ):= a⁻¹ -- from d ≤ e^ad /a
local notation "AP"=> (∫ A':Ids (mid P B), A0 (era A') Tp ∂depot (mid P B))
lemma rayY(a:ℝ)(h:0<a)(k:ℕ)(t:ℝ)(Yl:Support (Domain N B)): (coverNumber k Yl:ℝ) * currency k t Yl ≤ backX a * currency k (t+a) Yl :=by
 let I:ℝ:= coverNumber k Yl; unfold backX Trees.currency; rw [add_mul,Real.exp_add,mul_left_comm a⁻¹, mul_comm ((coverNumber k Yl):ℝ)]; have hp:I ≤ a⁻¹*Real.exp (a*I):=by rw [le_inv_mul_iff₀ h]; linarith only [Real.add_one_le_exp (a*I)]
 exact mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
include hρ ho hv₀ z pay hp hk hx
lemma leg_u (w:0 ≤ A0)(vK:0≤K₄) : (BudgetPoint.mass pp Yl.val (∑ i:Finset (Dwell (mid N B)),Scree.tariff pp o θ i * earnX pp F₁ u ρ x t k Yp Yl i)) ≤ K₄*(backX a * Zr)*(currency (radiusB x) (pp.supportExponent+a+a) Yl.val * AP):=by
 let V(v:pQ): Raid (Dwell (mid N B)):= Nor.linkY pp Yl.val (Yp (era v.val.2.2) (velt v.val.2.1.2 k t) (Stilo.beamH Yl.val)) (radiusB x); let P':= vV; haveI:= tour_p (S:=S) hρ; let U:= (U₄).restrict XQ; let f(i:pQ):= ∑ j:Finset (Dwell (mid N B)),P' j*V i j
 have hp'(j):Integrable (fun i=> V i j) U:= frill _ ((stamp_m (S:=S)).comp measurable_subtype_coe) (fun mx:↥(Sil S r)× ↥(tale S k t)=> Nor.linkY pp Yl.val (Yp mx.1 mx.2 Tp) (radiusB x) j) U
 have hp0: Integrable f U:= integrable_finsetSum _ fun i _=>(hp' i).const_mul _
 let zV:= Real.exp (pp.supportExponent * Cx)
 let R:= Zr; let G(i:pQ):=A0 (era i.val.2.2) Tp; let E(i:↥(Sil S r)):=A0 i Tp; let M:= AP
 have hx': Integrable G U:= frill _ (sill_m.comp (measurable_snd.snd.comp measurable_subtype_coe)) E U
 have hv: (BudgetPoint.mass pp Yl.val (∑ i:Finset (Dwell (mid N B)),P' i* earnX pp F₁ u ρ x t k Yp Yl i))=∫ i,zV*f i ∂U:=by unfold BudgetPoint.mass; rw [hk, integral_const_mul,show (∫ i,f i∂U)= ∑ j:Finset (Dwell (mid N B)),P' j*earnX pp F₁ u ρ x t k Yp Yl j from ?_]; refine (MeasureTheory.integral_finsetSum _ (fun i _=>(hp' i).const_mul _)).trans ?_; exact sum_congr rfl fun i _=>by unfold earnX; rw [integral_indicator (textR_m ..),integral_const_mul]
 have he:0≤ R:=by unfold R reserveT coin_n stilK; positivity; -- tune
 have hs:0≤ M:=integral_nonneg (fun i : Ids (mid P B)=>w _ _)
 change pp.mass Yl.val (∑ i:Finset (Dwell (mid N B)),P' i * earnX pp F₁ u ρ x t k Yp Yl i)≤ _; rw [hv]
 have hu(i:pQ): zV*f i≤ R*(Cζ*(G i)):=by
    let Y:= Yp (era i.val.2.2) (velt i.val.2.1.2 k t); have hT:= ripeB pp Yl.val θ (Y Tp) hk o ho (z _ _ _) hv₀ a hp
    unfold BudgetPoint.mass at hT; rw [hk] at hT; refine le_trans hT (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (show joinV (stake θ) (Y Tp) ≤ G i from pay _ _ _) (Real.exp_pos _).le) he)
 apply le_trans (integral_mono (hp0.const_mul _) ((hx'.const_mul _).const_mul R) hu)
 rw [integral_const_mul,integral_const_mul,show (∫ i:pQ,G i∂U)= _ from text_y F₁ u ρ hρ E]
 calc
    _ ≤ R*(Cζ*((Cx*K₄)*M)):= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx hs) (Real.exp_pos _).le) he
    _ = (R*K₄*M)*(Cx*Cζ):=by ring
    _ ≤ _:= (mul_le_mul_of_nonneg_left (rayY a hp (radiusB x) (pp.supportExponent+a) Yl.val) (by positivity : 0 ≤ R*K₄*M)).trans_eq (by unfold M R; ring)
end YM.CF.Jade

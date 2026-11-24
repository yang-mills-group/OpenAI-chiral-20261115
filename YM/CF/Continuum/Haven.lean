import YM.CF.Continuum.CostPath
import YM.CF.Continuum.Episode
import YM.CF.Continuum.CityGate
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Period
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
variable {d e η z g A B':ℝ} {j k k' m n l:ℕ}
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
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Salt Vow
set_option maxHeartbeats 800000
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0 k₀:ℕ)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)(R0 δ:ℝ→ℝ)
local notation "Lr"=>dleaf R.L
open CF.Mint MeasureTheory
open CF.Window
open Graph Window Jade.Earn

local notation "Bₓ" t=> cell t B R.L
include V in
lemma heir_s (y:ℝ)(j:ℕ): Scales.y SU.group R.L (hat R.L y j)=hat R.L y (j+1):=(hat_succ ..).symm
lemma same_room (N:Side): massMeter N=roomSite (More N):=by unfold massMeter roomSite; rw [site_card]; rfl
section
include V
lemma full_a (k:ℕ)(B M:Side) : 2*massMeter (cell M B R.L k) ≤ massMeter (cell M B R.L (k+1)):=by
 rw [same_room,same_room]; let X:= More (cell M B R.L k); let Y:= More (cell M B R.L (k+1)); let L:= R.L.val; have he:Y.val=X.val*L:=kint ..; have ht:2 ≤ L:=by unfold L; have h:=V.tallX; omega
 change 2*roomSite X ≤ roomSite Y; unfold roomSite; rw [site_card,site_card,he]; push_cast; rw [mul_pow,mul_comm (2:ℝ)]; apply mul_le_mul_of_nonneg_left _ (by positivity); exact le_trans (b:= ((2:ℝ)^4)) (by norm_num) (pow_le_pow_left₀ (by norm_num) (by exact_mod_cast ht) _)
private lemma gainBelow (x:ℝ)(t:0<x) (k:ℕ)(M B:Side) (A:GramM (cell M B R.L k))(D:GramM (cell M B R.L (k+1))) {C G:ℝ}(w:0≤G)(s:2*G≤C): budgetCharge D (soaked (hat R.L x (k+1))) (-C) ≤ budgetCharge A (soaked (hat R.L x k)) (-C)+curve_F R.L (More (cell M B R.L k)) (More (cell M B R.L (k+1))) (hat R.L x k) G:=by
 let a:= hat R.L x k; let b:= hat R.L x (k+1); let r:= cell M B R.L k; let p:= cell M B R.L (k+1); let C₀:=massMeter r; let F:=massMeter p
 have he:x≤a:= Vale.crown ..; have ha:a≤b:=by unfold a b hat; push_cast; linarith [Vale.pitch R.L]
 let X:=soaked a; let Y:=soaked b; have hx:Y ≤ X:= inv_anti₀ (Real.sqrt_pos.mpr (t.trans_le he)) (Real.sqrt_le_sqrt ha); have ht:0<Y:=by change 0<(Real.sqrt b)⁻¹; apply inv_pos.mpr; exact Real.sqrt_pos.mpr ((t.trans_le he).trans_le ha)
 have hi:strengthLog Y ≤ strengthLog X:= mul_le_mul_of_nonneg_left (Real.log_le_log ht hx) (Nat.cast_nonneg _)
 have hp:(0:ℝ)≤C₀:=zero_le_one.trans (money_pos _); have hz:2*C₀≤F:= full_a V ..; have hh:C₀≤F:= by linarith
 unfold curve_F pathFees; rw [heir_s V,←same_room,←same_room]
 change F*(3*strengthLog Y+-C) ≤ C₀*(3*strengthLog X+-C)+_
 change _ ≤ _+(3*(F-C₀)*strengthLog Y-G*F); nlinarith only [mul_le_mul_of_nonneg_left hi hp, mul_le_mul_of_nonneg_left s (show 0≤F-C₀ from sub_nonneg.mpr hh), mul_le_mul_of_nonneg_left hz w] -- ht
end
-- growth coupon assertion at this *same* cutoff, not any inclusive retuning uniform only given builders.
abbrev RootMoney (M:Side)(b:ℝ)(S:Session V a p i N0 J q h R0 δ x M l): Prop:= ∀ j<l, ‖Complex.exp (S.E (j+1)).v‖ * Real.exp (curve_F R.L (More (cell M B R.L j)) (More (cell M B R.L (j+1))) (hat R.L x j) b) ≤ ‖Complex.exp (S.E j).v‖
variable {CΩ K':ℝ} {M:Side} (s:0 < x)(u:0 ≤ CΩ)(w:2*CΩ ≤ K') (X:Session V a p i N0 J q h R0 δ x M l)
variable (Y:RootMoney V a p i N0 J q h R0 δ M CΩ X)(k_:Real.exp (budgetCharge (X.E 0) (soaked x) (-K')) ≤ rateBet (X.E 0) (X.Y 0) U)
include u w s Y k_
theorem fullPaid (j:ℕ)(p:j≤ l) : Real.exp (budgetCharge (X.E j) (soaked (hat R.L x j)) (-K')) ≤ rateBet (X.E j) (X.Y j) U:=by
 induction j with
 | zero=> rw [show hat R.L x 0=x by simp [hat]]; exact k_
 | succ j ih=>
    let Q:=budgetCharge (X.E j) (soaked (hat R.L x j)) (-K'); let L:= Complex.exp (X.E j).v; let L':= Complex.exp (X.E (j+1)).v; let β:= rateBet (X.E j) (X.Y j) U; let z:=curve_F R.L (More (cell M B R.L j)) (More (cell M B R.L (j+1))) (hat R.L x j) CΩ; let D:= partitionZ (X.E l) U (X.Y l)
    have ht:‖L‖* Real.exp Q ≤ ‖D‖:=by
       have he:=ih (by omega); unfold rateBet at he; rw [Complex.exp_neg,norm_mul,norm_inv,X.scale.balance j (by omega)] at he; exact (le_inv_mul_iff₀ (norm_pos_iff.mpr (Complex.exp_ne_zero _))).mp he -- balance ???
    unfold rateBet; rw [Complex.exp_neg,norm_mul,norm_inv,X.scale.balance _ p]
    apply le_trans (Real.exp_monotone (gainBelow V x s j M B _ _ u w)); rw [Real.exp_add]; apply (le_inv_mul_iff₀ (norm_pos_iff.mpr (Complex.exp_ne_zero _))).mpr
    calc
       _ = (‖L'‖*Real.exp z)*Real.exp Q:=by unfold L' z Q; ring
       _ ≤ _:= (mul_le_mul_of_nonneg_right (Y j p) (Real.exp_pos _).le).trans ht
end YM.CF.Py.Period

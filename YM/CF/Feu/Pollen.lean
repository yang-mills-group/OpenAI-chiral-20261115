import YM.CF.Feu.Hype
import YM.CF.Feu.Karma
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Feu
open Nor
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
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
local notation "S₁"=> (Domain N B)
local notation "dN"=> Directions SU.group (More N)
open Trees Footprint
variable (i:Roc (mid P B))(p:BudgetPoint) (l:ℕ)
local notation "old"=> (i.1.val.2)
local notation "Yp"=> (hostX (l:=l*k) S i)
local notation "ℓ"=> (l+5)
variable(u:0<k)(a:p.B≤ 2*k)
include u a
lemma veilK : (coverNumber k (hostX (l:=l*k) S i).val:ℝ) ≤ preCost ℓ+conversion S.ratio ℓ* coverNumber p.B i.1.val.2 := (le_trans (Nat.cast_le.mpr (Corona.cover_mono (inspected_price S.ratio _ k old u) k)) (footprint _ _ _ _ _ u a))
variable (F iT:ℝ)(Z:Real)(h:0 ≤ F)(Pu:BudgetPoint)(Y:0 ≤ iT)
local notation "J"=> (coverNumber p.B i.1.val.2)
include Y
lemma gore (Hp:reserve p.supportExponent iT (conversion S.ratio (l+5)) Z)(u':ℕ)(v:0≤g): (1+J:ℝ)^u' *currency k iT (hostX (l:=l*k) S i).val *g ≤ Real.exp (iT*preCost (l+5)) * (Z⁻¹^u'*u'.factorial*Real.exp Z)* Real.exp (-Z*J)* p.mass i.1.val.2 g:=by
 let b:ℝ:=↑J; let s:= p.supportExponent; let x:= Z⁻¹^u'*u'.factorial*Real.exp Z; let d:=iT*preCost (l+5); have hz:=Hp.2.1; have hx:0 ≤ x:=by unfold x; positivity
 have hu:currency k iT (hostX (l:=l*k) S i).val ≤ Real.exp (d+(s-2*Z)*b):=by
    apply Real.exp_monotone; apply (mul_le_mul_of_nonneg_left (veilK (S:=S) i p l u a) Y).trans; rw [mul_add]; apply add_le_add _ (le_trans (le_of_eq (mul_assoc ..).symm) (mul_le_mul_of_nonneg_right (by linarith only [Hp.2.2] : iT * conversion S.ratio (l+5) ≤ s-2*Z) (Nat.cast_nonneg _))); rfl
 refine (mul_le_mul_of_nonneg_right (mul_le_mul (polynomial_cost hz (Nat.cast_nonneg J) u') hu (Real.exp_pos _).le (mul_nonneg hx (Real.exp_pos _).le)) v).trans_eq ?_
 change x*Real.exp (Z*b)*Real.exp (d+(s-2*Z)*b)*g=Real.exp d*x*Real.exp (-Z*b)*(Real.exp (s*b)*g); rw [mul_comm _ x]; rw [mul_assoc x (Real.exp (Z*b)),←mul_assoc _ (Real.exp (s*b)), mul_assoc x (Real.exp d),←Real.exp_add,← Real.exp_add,mul_assoc x (Real.exp (d+_)),← Real.exp_add]
 rw [show Z*b+(d+(s-2*Z)*b)=d+ -Z*b+s*b from (by ring)]
omit a u Y
-- restore λ Solver.Volume Width poly allocated opacity.
abbrev leaps(j n:ℕ)(a:ℝ):= j.factorial*((j.factorial:ℝ)*1)* (2:ℝ)^j * (a⁻¹^(n*j)*(n*j).factorial*Real.exp a)
lemma leaseT(j n:ℕ)(P:BudgetPoint)(F:Track (Ride S) (Raid (Dwell (mid N B))))(z:Ride S)(k:ℕ)(p:P.power=n)(a':ℝ)(u:0<a')(A:ℝ)(h:0 ≤ A): Jet.composeCost j ((j.factorial:ℝ)*A) (brim P k (Stilo.bay z)) ≤ leaps j n a' *A * Real.exp (a' * coverNumber k (Stilo.bay z)):=by -- unused param F
 have hv:1 ≤ brim P k (Stilo.bay z):= one_le_pow₀ (le_add_of_nonneg_right (by positivity)); let c:=coverNumber k (Stilo.bay z); unfold Jet.composeCost; apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : 0 ≤ 1+brim P k (Stilo.bay z)) (show _ ≤ 2*brim P k (Stilo.bay z) by linarith) _) (by positivity)); unfold brim; rw [mul_pow,←pow_mul,p]; let C:= j.factorial*((j.factorial:ℝ)*1)*(2:ℝ)^j; let b:= a'⁻¹^(n*j)*(n*j).factorial*Real.exp a'; have hh:=polynomial_cost u (Nat.cast_nonneg c) (n*j); refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh (by positivity)) (by positivity)) ?_; unfold leaps; exact le_of_eq (by ring) -- tune
end YM.CF.Feu

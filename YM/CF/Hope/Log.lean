import YM.CF.Hope.Stair
import YM.CF.Feu.Jack
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Hope
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
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
open Ione Beau
local notation "N"=> P.order
local notation "Xo"=>Skye.Seat n
variable {F G:InkD n}{X₀:Scree.Hub n}
local notation "sR"=> X₀.val.2
local notation "sO"=> X₀.val.1
local notation "Fη"=> (Scree.tariff P sO h)
variable(p:PressB P X₀ F h a)(q:PressB P X₀ G h b)(hv:0 ≤ h)
open Larch
abbrev linen (P:BudgetPoint)(X₀:Scree.Hub n)(F:InkD n):= Beau.caj P X₀.val.2 (fun i x=> bixE (F x) i)
local notation "TL"=> linen P X₀ F
local notation "oar"=> (↑N+1:ℝ)
local notation "ξ"=> (P.order.factorial:ℝ)
variable(u:1≤h)(he:1≤(More n).val)
include p u
lemma coy_P (s:oar*a≤ 1/4): PressB P X₀ TL h (2*ξ*(oar*a)) ∧ ∀ V: Pane n,pingS P.threshold sR V→ NormedSpace.exp (TL V)-1=F V:=by
 have ht:0 ≤ a:= (Taxi.eraF _ _ p (zero_le_one.trans u) _ (ping_f P _)).grade
 let x:=oar*a; have hz:0≤ x:=by unfold x; positivity
 have hl:x<1:=lt_of_le_of_lt s (by linarith)
 let K(i:ℕ):=fun x'=> bixE (F x') i
 have hf(i):PressB P X₀ (K i) h (ξ*x^(i+1)):=by
    let J:= -F
    have hv:= powerF (ν_P p (zero_le_one.trans u)) (zero_le_one.trans u) (i+1)
    let k:ℝ:=-((1+(i:ℝ))⁻¹); have hp:|k| ≤ 1:=by unfold k; rw [abs_neg,abs_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α:=ℝ) i])
    rw [show K i=k • (J ^(i+1)) from (by funext x; unfold k K J bixE; rw [neg_smul]; simp)]
    exact hi_p (Ione.scale_E P hv k) (mul_le_of_le_one_left (show 0 ≤ ξ*x^(i+1) by positivity) hp)
 let T':= (fun i:ℕ=> ξ*x^(i+1)); have hh: Summable T':= ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hz hl)).mul_left _
 have hx:∑' i,T' i=ξ *x*(1-x)⁻¹:=by unfold T'; rw [tsum_mul_left]; simp_rw [pow_succ]; rw [tsum_mul_right,tsum_geometric_of_lt_one hz hl]; ring
 refine ⟨hi_p (shunt hf u hh) ?_, fun V hp=>?_⟩
 · rw [hx]; have h:0<1-x:=sub_pos.mpr hl; change ξ*x* _≤ 2*ξ*x; rw [←div_eq_mul_inv, div_le_iff₀ h]; nlinarith only [mul_le_mul_of_nonneg_left s (mul_nonneg (Nat.cast_nonneg (α:=ℝ) P.order.factorial) hz)] -- tune prove
 have hs:visible P sR ∅ V:= hates (by simpa using hp) -- namespace
 have hu:‖F V‖≤ a:=by
    obtain ⟨v,g,u',H⟩:= p.worth; refine le_trans (Pastry.lies u _) (le_trans ?_ H); unfold Pastry.tier; refine sum_le_sum fun i _=>?_ ; apply mul_le_mul ?_ ?_ (norm_nonneg _) (by have he:0 ≤ h:=zero_le_one.trans u; unfold Scree.tariff; positivity)
    · unfold Scree.tariff; exact le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans u) _) (one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _)))
    have he:=Prism.sig0 (u' _ hp i); simpa using he
 unfold linen; rw [pale_p V hs]; change exp (pencilT (F V))-1=_; rw [show NormedSpace.exp (pencilT (F V))=_ from text_K _ ((hu.trans (le_mul_of_one_le_left ht (by exact le_add_of_nonneg_left (by positivity)))).trans s)]; abel
local notation "ΘV"=> (fun x:Pane n=>NormedSpace.exp (F x)-1)
local notation "cQ"=> ξ*(Real.exp (oar*a)*(oar*a))
local notation "ζ"=> (b + ξ*((oar*b)*(oar*cQ)))
include q
-- dress arbitrary directional mark into linear log. G tangent + μres split separately.
lemma boot_X (x:oar*ζ ≤1/4) : ∃ V:InkD n, PressB P X₀ V h (2*ξ*(oar*ζ))∧ ∀ W:Pane n,pingS P.threshold sR W→ exp (V W)-1= G W*exp (F W):=by
 let D:InkD n:=ΘV; have he:=peer_P q (ε_P p (zero_le_one.trans u)) (zero_le_one.trans u); obtain ⟨v,z⟩:=coy_P (Larch.prop_add P X₀ q he) u x; refine ⟨_,v,fun W g=>(z W g).trans ?_⟩; change G W+G W*(_-1)=_; ring
end YM.CF.Hope
#print axioms YM.CF.Hope.boot_X

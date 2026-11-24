import YM.CF.Nor.Shock
import YM.CF.Nor.Paid
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Nor
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
local notation "B_"=> (More N)
local notation "S₁"=> (Domain N B)
local notation "dN"=> Directions SU.group (More N)
open Trees
local notation "X₁"=> Finset (Dwell N)
abbrev stilK(k:ℕ):ℝ:=5*(k+1:ℝ)
def coin_n (n m k:ℕ):ℝ:= stilK k^n * ((m.factorial:ℝ)* ((m.factorial:ℝ)*1) * ((2:ℝ)*stilK k^n)^m) -- coercions wrong
abbrev reserveT (n m k:ℕ)(a:ℝ):= coin_n n m k* (a⁻¹^(n+n*m)*(n+n*m).factorial*Real.exp a)
variable (P0:BudgetPoint) (U:Support (More N))
local notation "vX"=> liftR P0 U k 1
local notation "AX"=> surgeL P0 U k
lemma calendar : AX ≤ stilK k^P0.power*(1+(coverNumber k U:ℝ))^P0.power:=by unfold surgeL; rw [←mul_pow]; let B:=coverNumber k U; have ht:0≤(B:ℝ):=Nat.cast_nonneg _; let p:ℝ:=1+B; gcongr; unfold stilK; push_cast; nlinarith only [Nat.cast_nonneg (α:=ℝ) (coverNumber k U), Nat.cast_nonneg (α:=ℝ) k]
lemma coinPay(ε:ℝ)(h:0 < ε): AX*vX ≤ reserveT P0.power P0.order k ε*Real.exp (ε*coverNumber k U):=by
 let p:ℝ:= coverNumber k U; let G:=stilK k; let M:=P0.power; let n:=P0.order; have he:AX ≤ G^M*(1+p)^M:= calendar P0 U -- order tune
 have ht:1 ≤ AX:= by unfold surgeL; exact one_le_pow₀ (by apply le_add_of_nonneg_right; positivity)
 let Z:= G^M*(1+p)^M; have hz: 0 ≤ Z:= zero_le_one.trans (ht.trans he); have hx:vX≤ (n.factorial:ℝ)* ((n.factorial:ℝ)*1)*(2*Z)^n:=by unfold liftR Jet.composeCost; refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_trans (by linarith : 0≤ 1+ AX) (le_refl _)) (by unfold Z; linarith only [ht,he]) _) (by positivity)
 apply (mul_le_mul he hx (show 0≤vX by unfold liftR Jet.composeCost; positivity) hz).trans; let U':=coin_n M n k; have hh: Z*((n.factorial:ℝ)*(n.factorial*1)*(2*Z)^n)=U'*(1+p)^(M+M*n):=by unfold Z U' coin_n G; rw [pow_add, pow_mul]; ring -- tune constructors
 change Z*((n.factorial:ℝ)*_*_)≤ _; rw [hh]; refine (mul_le_mul_of_nonneg_left (polynomial_cost h (Nat.cast_nonneg (coverNumber k U)) (M+M*n)) (show 0 ≤ U' by unfold U' coin_n stilK; positivity)).trans_eq ?_; unfold reserveT; rw [← mul_assoc] -- tune
lemma ripeB (V₀:ℝ)(H: Raid (Dwell N))(p:P0.B=k)(o:Seat N)(h:o∈U)(t:0 ≤ H)(v:0 ≤ V₀)(e:ℝ)(u:0<e): P0.mass U (∑ i:Finset (Dwell N),Scree.tariff P0 o V₀ i*linkY P0 U H k i)≤ reserveT P0.power P0.order k e * (Trees.currency k (P0.supportExponent+e) U* joinV (stake V₀) H):=by
 let d':=joinV (stake V₀) H; have ht:0 ≤ d':=sum_nonneg (fun i _=> mul_nonneg ((stokes v).fee i) (t i)); have hp:= ((rate_i P0 U o h H k V₀ t v).trans (mul_le_mul_of_nonneg_right (coinPay P0 U e u) ht)); unfold BudgetPoint.mass; rw [p]; apply (mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le).trans_eq; unfold Trees.currency; rw [add_mul,Real.exp_add]; change _*_=_*(_* d'); ring -- tune
lemma vale_u (n m:ℕ)(e:ℝ): BoreP fun x=> reserveT n m (radiusB x) e :=by
 unfold reserveT coin_n stilK; let V:= ((BoreP.still 5).grip (BoreP.radius_c.join (BoreP.still 1))).self n; exact ((V.grip ((BoreP.still _).grip (((BoreP.still _).grip V).self m))).grip (BoreP.still _))
variable{ε:ℝ}
lemma prism_k{k:ℕ}{f:ℝ→ℝ}(p:sizeK R.L 1 f)(m n:ℕ)(x:∀ᶠ x in atTop,0 < f x∧ degreePrice (radiusB x) (f x) 1≤1/2): sizeK R.L (k+1) (fun x=>reserveT n m (radiusB x) ε* (f x * degreePrice (radiusB x) (f x) 1 ^ k * (1-degreePrice (radiusB x) (f x) 1)⁻¹)):=by
 let g:=fun x=>degreePrice (radiusB x) (f x) 1; have he:sizeK R.L k (fun x=>g x^k):= by simpa only [one_mul,g] using (apollo_d 1 p).square k
 let U':= fun x=>(1-g x)⁻¹; have hk:sizeK R.L 0 U':=(sizeK.mild R.L 2).cost_d (by
    filter_upwards [x] with x v; have hz:1/2≤1-g x:=by unfold g; linarith only [v.2]
    have hp:=lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) hz; unfold U'; rw [abs_of_pos (inv_pos.mpr hp), inv_le_iff_one_le_mul₀ hp,abs_of_pos (by norm_num : 0 < (2:ℝ))]; linarith)
 apply sizeK.low (n:=0+(1+k+0)) ?_ (by omega); exact ((vale_u n m ε).creditK R.L).tint ((p.tint he).tint hk)
end YM.CF.Nor

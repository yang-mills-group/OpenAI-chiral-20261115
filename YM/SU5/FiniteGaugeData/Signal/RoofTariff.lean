import YM.SU5.FiniteGaugeData.Reliance.Converted
import YM.SU5.FiniteGaugeData.LocalLimit.Replica.Bless
/-! # Convert heat comparison to strong high-level volume bills.

Sharp certificate throughout. Heat certificate s late uniformly on Y.Price cone (threshold UV
depends on s, and cone at row starts when kick paid); no new diagonal coupled with aperture claims.
Useful to transfer local sup & flag-weight budgets using this VERY partner (without its own election).
Heat beta at s is not sharp, but donor still has `Y.heatGap` `priceH.compare_density` etc and
has own raw `owns` and matching to x as used. -/
set_option autoImplicit false
set_option maxHeartbeats 420000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
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

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Chaff Gloss Maize Tye RP RP.Str Oise
namespace LocalLimit

open FullBill Window Marks
open Pyx
open Girt

namespace Preparation
local notation "q₀" => Chi.canonical
variable {P : Preparation} {F : (s:Side)→ Scree.Loom s → Prop} (Y:Course P F)

namespace Course
variable (i k j : ℕ)
local notation "Ξ" => Y.voyage i
local notation "U₀" => P.U
local notation "N₀" => (Ξ).funds
local notation "m₀" => Y.ir i
local notation "CS" => P.Ctor (Y.ir i)
local notation "kt" => Y.uv k
local notation "Xv" => (Ξ).X (Y.uv k)
local notation "Χ" j => (Xv).gram j
local notation "Qv" => (Ξ).CapeT
local notation "T" => Y.meter
local notation "Yr" => Vale.mesh m₀ P.R.L

open Window Graph Period Jade.Earn

variable (W:Cashbox P)
local notation "Ψ" k:max p:max=> (Y.voyage i).Q k p
local notation "Z" j:max p:max=> ((Y.voyage i).Q k p).gram j
local notation "X'" i:max=> hat P.R.L P.x i
-- height after s early (modified from Reliance/Converted and scaffold Carousel.fullPaid).
local notation "O"=> Classical.choice (YM.Next.Rank.exists_budget SU.group)
def admission (b C:ℝ)(j:ℕ):= C+b*(1/2:ℝ)^j
private lemma stair {a v b:ℝ} (e:2*a ≤ v)(w:0 ≤ b)(h:0 ≤ a) :
  let A:= (Y.sturdy i k).E j; let F:= (Y.sturdy i k).E (j+1);
  budgetCharge F (soaked (hat P.R.L P.x (j+1))) (-(admission b v (j+1))) ≤ budgetCharge A (soaked (X' j)) (-(admission b v j))+curve_F P.R.L (More (P.Ctor (Y.ir i) j)) (More (P.Ctor (Y.ir i) (j+1))) (hat P.R.L P.x j) a :=by
 intro A F; let x:=hat P.R.L P.x j; let y:=hat P.R.L P.x (j+1)
 have hw:x≤y:=by unfold x y hat; push_cast; linarith [Vale.pitch P.R.L]
 have hp:0<x:= (zero_lt_one.trans_le Y.oneP).trans_le (Vale.crown ..)
 let u:= massMeter (P.Ctor (Y.ir i) j); let z:= massMeter (P.Ctor (Y.ir i) (j+1))
 have hy: (Real.sqrt y)⁻¹ ≤ (Real.sqrt x)⁻¹ := inv_anti₀ (Real.sqrt_pos.mpr hp) (Real.sqrt_le_sqrt hw)
 have H: strengthLog (soaked y) ≤ strengthLog (soaked x):= mul_le_mul_of_nonneg_left (Real.log_le_log (inv_pos.mpr (Real.sqrt_pos.mpr (hp.trans_le hw))) hy) (Nat.cast_nonneg _)
 unfold curve_F pathFees; rw [heir_s P.V,←same_room,←same_room]; change z*(3*strengthLog (soaked y)+-(admission b v (j+1))) ≤ u*(_+-(admission b v j)) + (3*(z-u)*strengthLog (soaked y)- a*z)
 have hu: 0 ≤ u:=zero_le_one.trans (money_pos _); have hd:2*u ≤ z:= full_a P.V ..; let d:= b*(1/2:ℝ)^j; have ht: 0≤ d:= by unfold d; positivity
 rw [show admission b v (j+1)=v+d/2 from (by unfold admission d; rw [pow_succ]; ring), show admission b v j=v+d from rfl]; have h₁:0 ≤z-u:= by linarith
 change z*_ ≤ u*(3*strengthLog (soaked x)+_)+_; nlinarith only [mul_le_mul_of_nonneg_left H hu,mul_le_mul_of_nonneg_left e h₁,mul_le_mul_of_nonneg_right hd ht,mul_le_mul_of_nonneg_right hd h]

variable {a:ℝ}(v0:∀ x≥P.x,P.C x ≤ capCost P.R x a) (hv:0≤a)
include P Y v0
section x
local notation "X"=> Y.sturdy i k
variable (p:(Y.voyage i).kick ≤ k){v:ℝ}(hp:2*a≤v)
local notation "b"=> |Y.τ|
include p hp hv
lemma lamphead (t:j≤Y.uv k):
    Real.exp (budgetCharge (Χ j) (soaked (X' j)) (-(admission |Y.τ| v j))) ≤ rateBet (Χ j) (Qv j) P.U:=by
 induction j with
 | zero=> rw [show hat P.R.L P.x 0=P.x by simp [hat]]; exact tenure Y i k p (by unfold admission; rw [pow_zero,mul_one]; exact (le_abs_self _).trans (le_add_of_nonneg_left (by linarith))) -- add?
 | succ j ih=>
    let Q:=budgetCharge (Χ j) (soaked (X' j)) (-(admission b v j)); let L:= Complex.exp (Χ j).v; let L':=Complex.exp (Χ (j+1)).v
    let z:=curve_F P.R.L (More (P.Ctor (Y.ir i) j)) (More (P.Ctor (Y.ir i) (j+1))) (hat P.R.L P.x j) a; let D:= partitionZ (Χ (Y.uv k)) P.U (Qv (Y.uv k))
    have hh:‖L‖ * Real.exp Q ≤ ‖D‖:= by
       have he:=ih (by omega); unfold rateBet at he; rw [Complex.exp_neg,norm_mul,norm_inv,(Xv).balance j (by omega)] at he; exact (le_inv_mul_iff₀ (norm_pos_iff.mpr (Complex.exp_ne_zero _))).mp he
    unfold rateBet; rw [Complex.exp_neg,norm_mul,norm_inv,(Xv).balance _ t]; let K:=stair Y i k j hp (abs_nonneg Y.τ) hv
    apply le_trans (Real.exp_monotone K); rw [Real.exp_add]; apply (le_inv_mul_iff₀ (norm_pos_iff.mpr (Complex.exp_ne_zero _))).mpr
    calc _ = (‖L'‖*Real.exp z)*Real.exp Q := by change ‖L'‖*(Real.exp Q*Real.exp z)=_; ring
         _ ≤ _ := (mul_le_mul_of_nonneg_right (show ‖L'‖*Real.exp z≤‖L‖ from paid_progress Y i k v0 j t) (Real.exp_pos _).le).trans hh
end x

def fullTariff (P:Preparation)(a:ℝ) := (|Carousel.costPlan P.V (cashU P.W.C) O|+ 2*|a|) + 3
local notation "C'"=> fullTariff P a
local notation "B"=> Carousel.costPlan P.V (cashU P.W.C) O
include W hv
lemma rooted : ∀ᶠ j:ℕ in atTop,
    (∀ i k,(Y.voyage i).kick ≤ k → j ≤ Y.uv k → Tableau (mesh (Y.ir i) P.R.L j) (((Y.voyage i).X (Y.uv k)).gram j) ((Y.voyage i).CapeT j) P.U (soaked (X' j)) (fullTariff P a)) ∧
    ∀ᶠ k:ℕ in atTop,j<buoy (Y.ivory k) ∧ ∀ i:ℕ,∀ p:(Y.voyage i).kick ≤ k,
        Tableau (mesh (Y.ir i) P.R.L j) (((Y.voyage i).Q k p).gram j) ((Y.voyage i).CapeT j) P.U (soaked (X' j)) (fullTariff P a):=by
 let A:= C'-1; have hC:A+1≤ C':=by unfold A; linarith; -- tune
 have hp2:B≤ C':=by unfold fullTariff; linarith [le_abs_self B, abs_nonneg a]
 have hp : 2*a < A := (by unfold A fullTariff; linarith only [abs_nonneg B, le_abs_self a]); -- tune
 have ht:Tendsto (fun i:ℕ=>admission |Y.τ| (2*a) i) atTop (𝓝 (2*a)):=by simpa only [admission,mul_zero,add_zero,Function.comp_def] using ((tendsto_const_nhds (x:=2*a)).add ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(1:ℝ)/2) (by norm_num)).const_mul |Y.τ|))
 filter_upwards [ht.eventually (ge_mem_nhds hp)] with j f; have B₁ (i k:ℕ)(p:(Y.voyage i).kick ≤ k)(hj:j ≤ Y.uv k): Real.exp (budgetCharge (((Y.voyage i).X (Y.uv k)).gram j) (soaked (X' j)) (-A)) ≤ rateBet (((Y.voyage i).X (Y.uv k)).gram j) ((Y.voyage i).CapeT j) P.U :=by
      let G:=((Y.voyage i).X (Y.uv k)).gram j; exact (Real.exp_monotone (budgetLe G _ _ _ (neg_le_neg f))).trans (lamphead Y i k j v0 hv p le_rfl hj)
 constructor
 · intro i k p t; let g:=((Y.voyage i).X (Y.uv k)).gram j; let p':= W.choose_spec.2 _ (Vale.crown P.R.L P.x j); refine ⟨Carousel.sailed P.V 1 2 6 P.N0 P.J q₀ P.h P.R0 P.δ (Y.sturdy i k) j t, (Real.exp_monotone (budgetLe g _ _ _ (neg_le_neg (show A≤ C' by linarith)))).trans (B₁ i k p t), (Carousel.toils_κ P.V 1 2 6 P.N0 P.J q₀ P.h P.R0 P.δ P.height (Y.sturdy i k) O j t p'.2.1 p'.2.2).trans (Real.exp_monotone (budgetLe g _ _ _ hp2))⟩
 · filter_upwards [near_room Y j A,Y.heatGap j] with k u hz
   refine ⟨hz.1,fun i p=>?_⟩; let H:= ((Y.voyage i).Q k p); let m:=Y.ir i; let k':=Y.ivory k
   let Vc:= H.carnival ((Y.voyage i).funds); let V:=Vc.E j; let z:=Vc.Y j; let x:= ((Y.voyage i).X (Y.uv k)).gram j; let y:=hat P.R.L P.x j; let d:= soaked y
   have ht:j ≤ Y.uv k:=(hz.1.trans (deeper ..)).le
   let G:=hz.2 i p; have hP:= B₁ i k p ht; have hpr:= W.choose_spec.2 y (Vale.crown ..)
   let Zx:=compensated P.U x z; let Zy:=compensated P.U V z
   have he: ‖Zx-Zy‖ ≤ Real.exp (budgetCharge x d (-A))/2:= (vacuum_compare P.V G.priceA (G.priceH.permits) G.compare_density).trans (u i p)
   refine ⟨?_,?_,?_⟩
   · exact Carousel.sailed P.V 1 2 6 P.N0 P.J q₀ P.h P.R0 P.δ Vc j hz.1.le
   · have hh:Real.exp (budgetCharge x d (-A)) ≤ ‖Zx‖:= hP
     change Real.exp (budgetCharge V d (-(fullTariff P a))) ≤ ‖Zy‖; refine (Real.exp_monotone (budgetLe V _ _ d (neg_le_neg hC))).trans ?_; apply le_trans (diffuser Y i j d A V x); linarith [norm_sub_norm_le Zx Zy]
   exact (Carousel.toils_κ P.V 1 2 6 P.N0 P.J q₀ P.h P.R0 P.δ P.height Vc O j hz.1.le hpr.2.1 hpr.2.2).trans (Real.exp_monotone (budgetLe V _ _ d (show B≤ fullTariff P a from hp2)))
end Course
end Preparation
end LocalLimit
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.Course.rooted

import YM.CF.Song.Beat
import Zephyr.Poly
import Zephyr.Basic
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue Haro Ione BondL Larch Glyph
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial

open Zephyr
theorem spanGain (k:ℕ) : 1 ≤ spanV k:= by
  unfold spanV
  exact_mod_cast (Nat.one_le_pow 4 (k+k+1) (by omega))

theorem aimGain (k:ℕ) {a L:ℝ}(u:0<a)(v:0≤L) : 1 ≤ aimV k a L:=by
 have w:0≤Tenant.quota:=(by norm_num : (0:ℝ)≤16).trans quota_bound
 refine one_le_mul_of_one_le_of_one_le (spanGain k) (one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by positivity)) ?_)
 have h:= (fund_hit _ _ u w).le_tsum 0 (fun i _=> by positivity)
 simp only [Nat.cast_zero,mul_zero,Real.exp_zero,zero_add,one_pow,mul_one,one_mul] at h
 exact ((by norm_num:(1:ℝ)≤16).trans quota_bound).trans h

abbrev crystalConst (m n:ℕ)(r:ℝ):= tollL0 m n (r+1)*Tenant.quota*(16*fernL (4+coinK m n))

theorem crystalPos (m n:ℕ)(r:ℝ) : 0 ≤ crystalConst m n r:=by
 have w:0≤Tenant.quota:=(by norm_num : (0:ℝ)≤16).trans quota_bound
 unfold crystalConst tollL0 fernL gown
 positivity
def iceRent (b:ℕ):=crystalConst 6 2 1 * (b:ℝ)^(4+coinK 6 2+1)

theorem polIce : Poly iceRent := (Zephyr.pol _).mul (blockPol.pow _)
theorem iceRentZen (b:ℕ) : 0 ≤ iceRent b := mul_nonneg (crystalPos ..) (pow_nonneg (Nat.cast_nonneg b) _)

namespace Pace
variable {a b c W r γ d S v α θ z ζ Wk:ℝ}(h:Pace P a b c W r γ d S v α θ z ζ Wk)
include h
lemma addRate : 2*(P.supportExponent+1)*Fief.tileN 1≤ a/2*P.B :=by
 have j:=h.nf
 unfold wu Fief.tileN at j
 unfold Fief.tileN
 push_cast at j ⊢
 linarith only [j,P.exponent_pos]
lemma req (q:0<a): a⁻¹ ≤ (P.B:ℝ):=by
 refine le_of_mul_le_mul_right ?_ q
 rw [inv_mul_cancel₀ q.ne']
 have j:=h.addRate
 unfold Fief.tileN at j
 push_cast at j
 linarith only [j,P.exponent_pos]

lemma capPoint (q:0<a) (ε:ℝ)(t:0≤ε)(u:ε≤5*b+c)
    (h0:P.order=6)(h1:P.power=2)(h2:P.supportExponent=1):
    cap2 (plusP P) ε W a ≤ iceRent P.B:=by
 let T:=(P.order+1:ℝ)*W^2
 have tm : 0≤T:= by unfold T;positivity
 have tp:T*ε≤1:=calc
    _ ≤ (T*aimV P.B a (wu P+2))*(5*b+c) := mul_le_mul
      (le_mul_of_one_le_right tm (aimGain _ q (by unfold wu; linarith [P.exponent_pos])))
      u t (tm.trans (le_mul_of_one_le_right tm (aimGain _ q (by unfold wu;linarith [P.exponent_pos]))))
    _ ≤ d := h.fee
    _ ≤ spanV P.B*d:= le_mul_of_one_le_left h.zen (spanGain _)
    _ ≤ 1:= h.endP.trans (by norm_num [wΨ])
 rw [show cap2 (plusP P) ε W a = (T*ε)*(crystalConst P.order P.power P.supportExponent*(a⁻¹)^(4+coinK P.order P.power+1)) from ?_]
 apply le_trans (mul_le_of_le_one_left (mul_nonneg (crystalPos ..) (by positivity)) tp)
 have t' := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr q.le) (h.req q) (4+coinK P.order P.power+1)) (crystalPos P.order P.power P.supportExponent)
 rw [iceRent]
 exact t'.trans_eq (by rw [h0,h1,h2])

 change T*((tollL0 P.order P.power (P.supportExponent+1)*Tenant.quota)*ε*(16*fernL (4+coinK P.order P.power) * (a⁻¹)^(4+coinK P.order P.power+1))) = _
 unfold crystalConst
 ring
end Pace
end YM.CF.Sour

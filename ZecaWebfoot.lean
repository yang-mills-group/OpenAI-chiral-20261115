import ZecaRobin
import ZecaCosi
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Λ"=> P.par
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)

local notation "z'"=> Yoke.witnessZ
local notation "κ"=>P.sidesPerTick
local notation "κz"=> (P.sidesPerTick:ℤ)

variable (x : P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "M"=> P.ColorHil 3 (ξ)
local notation "G"=> P.ManyF 3 (ξ)
local notation "Ω"=> P.colorZero 3 ξ
local notation "Γ"=>P.cartage 3 ξ
local notation "Η"=>P.seasons 3 ξ
local notation "π"=>P.wealth 3 ξ
local notation "Πγ"=>P.enter 3 ξ
local notation "ω"=> P.heaven 3 ξ
open Regis.Circuit -- Aster





local notation "Era" r:max=>P.pointEra r
local notation "L"=>P.par.R.L
/-- direct scaled error if λ=0 impossible, so divided. -/
def inkLoss(A:ℝ)(r:ℕ):=
 P.plumeK r * ((4 * violet P.par (P.pointEra r) A)
     / zoomM P.par.R.L ^(r-P.pointEra r))

variable(A:ℝ)
lemma web_cost:
 ∀ᶠ r:ℕ in atTop, P.inkLoss A r = ((κ:ℝ)^4/P.petalsK r^2)*
      (4*Real.exp (8*A+1)) * P.repeatLoss r :=by
 apply Eventually.of_forall; intro r
 unfold inkLoss repeatLoss plumeK rewardK violet
 change ((κ:ℝ) * (P.plannedK r:ℝ))^4 / _ * _ =
     _ * _ * (((P.plannedK r:ℝ)^4/P.tallWorth r)*_/_)
 ring

lemma inkLoss_zero: Tendsto (P.inkLoss A) atTop (𝓝 0):=by
 let d:= (κ:ℝ)^4 /(1/2:ℝ)^2
 let b:=d*(4*Real.exp (8*A+1))
 have h:Tendsto (fun r:ℕ=>b*P.repeatLoss r) atTop (𝓝 0):=mul_zero b ▸ P.era_complete.const_mul b
 have g:∀ᶠ r:ℕ in atTop,0<P.repeatLoss r:=by
   filter_upwards [P.reward_positive, P.future_payment.eventually P.size_honors] with r p q
   exact div_pos (mul_pos (p.2 _) q.1) (pow_pos (zoomM_p _) _)
 refine squeeze_zero' ?_ ?_ h

 · filter_upwards [P.web_cost A,g] with r t z
   rw [t]; positivity
 filter_upwards [P.web_cost A,g] with r t z
 have p:=P.petal_floor r
 have q:0<P.petalsK r:=lt_of_lt_of_le (by norm_num) p
 rw [t]; unfold b d; gcongr

section
variable {α:Type*}[NormedAddCommGroup α][NormedSpace ℂ α]
lemma rescaleNick {m ν z k:ℝ}{X Y:α}
    (d:dist X ((m:ℂ) • Y) ≤ ‖(m:ℂ)‖*ν/z)
    (p: m ≠ 0) (q:0≤k):
  ‖((k:ℂ) / (m:ℂ)) • X - (k:ℂ) • Y‖≤ k*(ν/z):=by
 have t:(m:ℂ)≠0:= by exact_mod_cast p
 rw [←show ((k:ℂ)/(m:ℂ)) • ((m:ℂ) • Y)=(k:ℂ) • Y by
           rw [smul_smul, div_mul_cancel₀ _ t],
    ← smul_sub, norm_smul, ← dist_eq_norm,norm_div,Complex.norm_real (r:=k), Real.norm_of_nonneg q]
 refine (mul_le_mul_of_nonneg_left d (div_nonneg q (norm_nonneg _))).trans_eq ?_
 rw [mul_div_assoc, ←mul_assoc,div_mul_cancel₀ _ (norm_ne_zero_iff.mpr t)]
end
#print axioms rescaleNick

import ZecaBrood
import ZecaArch
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




lemma ruby_rightWing (z:Vantage)(D:P.Apron)(a b:ℝ):
  P.ruby 3 ξ D z a b ω= Γ z (π (P.beamRaw 3 x D a)):=by
 let h:=(a-D.realWidth P 3).toNNReal
 let q:=D.engine P 3 ξ
 have hg:Πγ ω=Ω:=rfl
 rw [P.ruby_price]
 change ((Η).E h) (Γ z ((P.coffer 3 ξ q)
     (Γ (-z) ((Η).E _ ω)))) = _
 rw [P.heaven_hot,P.cart_empty,P.warm_drive]
 -- sign warm_drive
 change Γ z ((Η).E h (π (q (Πγ ω))))= _
 rw [hg]
 exact congrArg (Γ z) (P.bankHeat ..).symm
def warpPose(r:ℕ)(p:Plume_LocalFieldBounds):Vantage:=P.jetS r • p.pose
abbrev warpf(f r:ℕ)(p:Plume_LocalFieldBounds):=P.jetS r*p.tar+ P.granPos f r [] 3
private lemma tiny_stem'(n:ℕ):
 0≤P.gPosition r (P.granule n) 3:=by
 let u:ℝ:= (P.granule n 3:ℝ)
 have ht:0≤u:= (P.tiny_one_ledger r (n:ℤ)).1
 exact (div_nonneg (mul_nonneg ht (P.macroStep_pos r).le) (Nat.cast_nonneg _))

lemma fly_time_stem : 0 ≤ P.granPos f r [] 3:=by
 unfold granPos
 rw [pivotQ]
 exact P.tiny_stem' _
lemma warpPos_hot(p:Plume_LocalFieldBounds):0<P.warpf f r p:=
 add_pos_of_pos_of_nonneg (mul_pos (P.jetS_pos r) p.hot) (P.fly_time_stem (f:=f) (r:=r))

-- recentered chick, not unshifted. Chi proxy
def plover (f r:ℕ) (p:Plume_LocalFieldBounds): G:=
 let a:=P.warpf f r p
 Γ (P.warpPose r p)
     ((P.plumeK r:ℂ) • P.crop 3 x f r [] a a ω)

lemma cart_expandwing (a b:Vantage)(u:G):
 Γ (a+b) u= Γ a (Γ b u):=by rw [P.cart_paves]; rfl
lemma cart_tandem (z:Vantage)(u v:G):
 inner ℂ (Γ z u) (Γ z v)=inner ℂ u v:=by
 rw [←ContinuousLinearMap.adjoint_inner_left,P.cart_reverses,
     ←P.cart_expandwing,neg_add_cancel,P.cart_zero]; rfl

variable (p q:Plume_LocalFieldBounds) (W₀:5∣P.par.R.L.val)

include W₀
lemma plover_cost: ∀ᶠ r:ℕ in atTop,
 P.plover x f r p= Γ (-P.granPos f r []) (P.chick x f p r):=by
 filter_upwards [P.spaced_poses W₀ p] with r h
 let u:=P.spacedPitch r p
 have hx:P.laysM (P.vtile r u)=P.warpPose r p:=h
 have hu:P.warpf f r p-P.granPos f r [] 3=P.meshPose r u 3:=
    (add_sub_cancel_right ..).trans (congrFun h 3).symm
 unfold chick finch fly
 rw [map_smul,map_smul]
 unfold plover crop
 dsimp only
 rw [P.ruby_rightWing,hu,map_smul, ←P.cart_expandwing]
 rw [add_zero,beamGridRay,P.commit_move,hx,←P.cart_expandwing,add_comm (P.warpPose r p)]
 rfl
variable {seq:ℕ→ℕ}(T:P.Nepenthe seq x) (J:P.Ellis 3 x)
include T J
lemma plover_gram:
 Tendsto (fun i=> inner ℂ (P.plover x f (seq i) p) (P.plover x f (seq i) q)) atTop (𝓝 (lyric p q)):=by
 refine (P.flying_gram f x p q W₀ J T).congr' ?_
 filter_upwards [T.sky.eventually (P.plover_cost (f:=f) x p W₀), T.sky.eventually (P.plover_cost (f:=f) x q W₀)]
    with i a b
 rw [a,b,P.cart_tandem]
#print axioms Spine.plover_gram

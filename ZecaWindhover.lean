import ZecaMerlin
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





open _root_.YM.ZecaSky


variable {b:Axis} (hb:b≠3){a c:ℝ}
local notation "O"=> Option (brig a c)
local notation "Δ"=>ZecaSky.pitch (beam5 a c)
def sh (hb:b≠3)(p:Plume_LocalFieldBounds)(k:Option (brig a c)) (r:ℕ):Cover:=
   P.spacedPitch r (falling hb p k)-P.spacedPitch r p

/-- copied actor. -/
lemma sk_copied(p:Plume_LocalFieldBounds)(k:O):
  P.chartAll (P.sh hb p k r) (P.hawthorn x f r p) =
        P.hawthorn x f r (falling hb p k):=by
 unfold hawthorn issuing sh
 rw [map_smul,P.chart_ids,sub_add_cancel]

variable (p:Plume_LocalFieldBounds) (k:Option (brig a c)) (W₀:5∣P.par.R.L.val)
include W₀
lemma sk_moving:
 ∀ᶠ r:ℕ in atTop,
 P.meshPose r (P.sh hb p k r)= P.jetS r • towardLeft b (Δ k):=by
 filter_upwards [P.spaced_poses W₀ p,P.spaced_poses W₀ (falling hb p k)] with r g j
 rw [falling_pose,smul_add,←g] at j
 rw [eq_sub_of_add_eq' j.symm]
 -- tune
 funext i
 rw [Pi.sub_apply, pose_w,pose_w,pose_w, sh,Pi.sub_apply,Int.cast_sub, _root_.sub_mul]
#print axioms sk_moving

omit W₀
/-- price certificate on these data.
Use phases in the UV d units; y= u δ_n gives physical-phase version. -/
def flagging (f:ℕ) (hb:b≠3)(p:Plume_LocalFieldBounds)(k:O)(r:ℕ):Prop:=
 let q:=falling hb p k
 P.meshPose r (P.sh hb p k r)= P.jetS r • towardLeft b (Δ k) ∧
 P.hawthorn x f r q=P.chartAll (P.sh hb p k r) (P.hawthorn x f r p) ∧
 P.Ledge x r (P.hawthorn x f r q) sunstep (P.singer x f q r) ∧
 (p.pose b < Δ k → P.Ledge x r (P.hawthorn x f r q) (moonstep b)
                         (P.singer x f q r))

include W₀
lemma flagged: ∀ᶠ r:ℕ in atTop, P.flagging x f hb p k r:=by
 filter_upwards [P.sk_moving hb p k W₀,
    P.occupies (b:=b) f x (falling hb p k) W₀] with r h j
 refine ⟨h, (P.sk_copied x hb p k).symm,j.1,fun i=>j.2 ?_⟩
 rw [falling_pose,Pi.add_apply,towardLeft,if_pos rfl,← sub_eq_add_neg]
 exact sub_neg.mpr i
#print flagging

import ZecaBrant
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


variable (p:Plume_LocalFieldBounds)(W₀:5∣P.par.R.L.val)

def mWarp(f r:ℕ)(p:Plume_LocalFieldBounds) :ℝ:= P.jetS r*p.tar-P.granPos f r [] 3
def mPlover (f r:ℕ) (p:Plume_LocalFieldBounds): G:=
 let a:=P.mWarp f r p
 Γ (P.warpPose r p)
     ((P.plumeK r:ℂ) • star (P.crop 3 x f r [] a a) ω)

include W₀
#check P.cart_mirror
lemma mPlover_cost: ∀ᶠ r:ℕ in atTop,
 P.mPlover x f r p= Γ (-P.granPos f r []) (π (P.pod f x p true r)):=by
 filter_upwards [P.spaced_poses W₀ p] with r h
 let u:=P.spacedPitch r p
 have hx:P.laysM (P.vtile r u)=P.warpPose r p:=h
 have hu:P.mWarp f r p+P.granPos f r [] 3=P.meshPose r u 3:=
    (sub_add_cancel ..).trans (congrFun h 3).symm
 unfold pod grackle
 rw [map_smul,map_smul]
 unfold mPlover crop
 dsimp only
 rw [P.ruby_twin,P.ruby_rightWing,P.cart_mirror,hu,map_smul, ←P.cart_expandwing]
 rw [add_zero,beamGridRay,P.commit_move,hx,←P.cart_expandwing,add_comm (P.warpPose r p)]
 rfl

variable {seq:ℕ→ℕ} (N:P.Umber x seq)
include N

lemma white_mates :
 Neighbor (fun i=>P.mPlover x f (seq i) p) (fun i=>P.plover x f (seq i) p) :=by
 have h:=fam_dist (P.brant_go f x true true p W₀ N)
   (P.brant_go f x true false p W₀ N) (P.brant_go f x false false p W₀ N)
 refine squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) ?_ h
 filter_upwards [N.sky.eventually (P.mPlover_cost (f:=f) x p W₀),
    N.sky.eventually (P.plover_cost (f:=f) x p W₀)] with i a b
 rw [a,b,←map_sub,P.cart_norm,chick,←map_sub]
 exact P.bank_cost 3 ξ _
#print axioms white_mates

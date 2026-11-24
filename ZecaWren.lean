import ZecaTern
import ZecaNova
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






variable (f)
   (F:P.Nib 3 (P.advocate 3 x 3))
   (c:ℕ→ℂ)
   (error:ℕ→ℝ)

def Nick:Prop:=
 ∀ᶠ r:ℕ in atTop,∀ a b:ℝ,P.rosePad 3 (P.pointEra r)≤a→P.rosePad 3 (P.pointEra r)≤b→
 ‖(c r) • F a b - (P.plumeK r:ℂ) • P.crop 3 x f r [] a b‖≤error r

lemma rose_wider (m:ℕ) : (P.rosePad 3 m)≤P.macroStep m*(P.baseK m* (P.roof:ℝ)):=by
 let n:=P.axleQ 3 (P.thresholdF m)
 have hp : P.roseWide 3 m ≤ P.baseK m*(P.roof):=by
    change 4*n+P.roseFlat≤(2*n+1)*(8+P.roseFlat)
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_add (2*n)]
    omega
 rw [← Nat.cast_mul,mul_comm]
 exact mul_le_mul_of_nonneg_right (show _ from Nat.cast_le.mpr hp) (P.macroStep_pos _ |>.le)

lemma warpf_fits (p:Plume_LocalFieldBounds) (v:(P.roof:ℝ)≤p.tar):
 P.rosePad 3 (P.pointEra r)≤P.warpf f r p:=
   calc
    _ ≤ _ := P.rose_wider _
    _ = P.jetS r * (P.roof:ℝ) :=by rw [P.jetS_base,mul_assoc]
    _ ≤ P.jetS r*p.tar :=mul_le_mul_of_nonneg_left v (P.jetS_pos _|>.le)
    _ ≤ _:=le_add_of_nonneg_right P.fly_time_stem

lemma Nick.loftIt {P:Spine}{f:ℕ}{x:P.Spectrum0 3}{F:P.Nib 3 (P.advocate 3 x 3)}
 {c:ℕ→ℂ}{error:ℕ→ℝ}(n:P.Nick f x F c error)
 (b0:P.Bottle 3 (P.advocate 3 x 3) F)
 (e0:Tendsto error atTop (𝓝 0)){seq:ℕ→ℕ}(s': Tendsto seq atTop atTop):
 P.Loft f x F c seq:=by
 let ω₁:=P.heaven 3 (P.advocate 3 x 3)
 have e:=(e0.comp s').mul_const ‖ω₁‖
 rw [zero_mul] at e
 refine ⟨b0,fun p hp=>?_⟩
 refine squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) ?_ e
 filter_upwards [s'.eventually n] with i t
 have h:=P.warpf_fits (r:=seq i) f p hp
 specialize t _ _ h h
 refine le_trans ?_ (mul_le_mul_of_nonneg_right t (norm_nonneg _))
 simp only [Function.comp_apply,kestrelTilt,kestrelRig,kestrelSeed,plover,
     ← map_sub,P.cart_norm]
 exact ContinuousLinearMap.le_opNorm
    ((c (seq i)) • F _ _ - (P.plumeK (seq i):ℂ) • P.crop 3 x f (seq i) [] _ _) _
#check @Nick.loftIt

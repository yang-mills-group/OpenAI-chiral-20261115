import ZecaPuffin
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

open Hierarchy.Seld.Zeca
open Hierarchy.Seld (parabola)
open OS.Semigroup
open Boundary

local notation "Δr"=> P.jetS
variable (F:P.Nib 3 (P.advocate 3 x 3)) (sc:ℕ→ℂ)(seq:ℕ→ℕ)(d:Vantage)


variable (D:Hierarchy.Seld.Zeca.Moment (P.ManyF 3 (P.advocate 3 x 3)))


local notation "F'"=>P.twinNib 3 ξ F
structure Jubilee
     (sc:ℕ→ℂ)(seq:ℕ→ℕ)
     (D:Hierarchy.Seld.Zeca.Moment (P.ManyF 3 (P.advocate 3 x 3)))
     (d:Vantage)(T:ℝ)(W:ℕ→ℝ→ℂ):Prop where
 normal:Breakwater (P.Calvados x sc seq d D) T W d
 contrary:Breakwater (P.Calvados x (star sc) seq (-d) D.dagger) T (Tow W) (-d)
 spacelike:
    Tendsto (fun i=>P.Mimosa x sc seq d D T (W 0) i -
     P.Mimosa x (star sc) seq (-d) D.dagger T (Tow W 0) i) atTop (𝓝 0)
variable (q:P.Truth 3 (P.advocate 3 x 3) F D)
   (T:ℝ)(W:ℕ→ℝ→ℂ)
include q
theorem terrine
 (p:P.Bottle 3 (P.advocate 3 x 3) F)
 (p':P.Bottle 3 (P.advocate 3 x 3) (P.twinNib 3 (P.advocate 3 x 3) F))
 (u:P.Mach x F sc seq)
 (v:P.Ebb x F sc seq)

 (u':P.Mach x (P.twinNib 3 (P.advocate 3 x 3) F) (star sc) seq)
 (v':P.Ebb x (P.twinNib 3 (P.advocate 3 x 3) F) (star sc) seq)
 (e:d 3=0)(h:Pentadose d)
 (a:0<T)(b:T<heartscale d)
 (w:Temporal T W) :
 P.Jubilee x sc seq D d T W:=by
 have h0:=P.amaro x F sc seq d D q T W p u v e h a b w
 have h1:=P.amaro x _ (star sc) seq (-d) D.dagger q.twin T (Tow W) p' u' v'
        (by simp [e]) h.negative a
        (show T < ‖-(WithLp.toLp 2 d:Gaia)‖ by rw [norm_neg];exact b)
        w.tow
 exact ⟨h0,h1,cordialDiff T W d a h0 h1⟩
#print axioms terrine

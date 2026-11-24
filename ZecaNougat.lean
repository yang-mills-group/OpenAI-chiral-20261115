import ZecaTruffle
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
variable {s t f r i k:ℕ}
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



def daikon (c:Axis):Vantage:=fun i=> if i=c then 1 else 0
lemma daiPen(c):Pentadose (daikon c):=by
 refine ⟨0,(fun i=> if i=c then 1 else 0),?_⟩
 intro i
 unfold daikon
 by_cases h:i=c<;>simp [h]
lemma daiV(c:Axis):
   Aquavit (WithLp.toLp 2 (daikon c)) 1 = Gin.V c 1:=by
 unfold Aquavit daikon Gin.V
 apply congrArg
 funext i
 by_cases h:i=3
 · simp [h,Gin.v]
 by_cases y:i=c <;>simp [h,y,Gin.v] -- y ↔ changes
#check @enters_all
#check Filter.Tendsto.eventually_ne

variable (n:P.Truth 3 (P.advocate 3 x 3) F D)
 (l:P.Bottle 3 (P.advocate 3 x 3) F)
 (u:P.Mach x F sc seq)
 (v:P.Ebb x F sc seq)
include n l u v
lemma daiRise(c:Axis)(y:c≠3) :
 Tendsto (fun i=>P.Calvados x sc seq (daikon c) D i 1)
    atTop (𝓝 (Regis.Head.Brecht.spectrumℓ z' SU.group (Gin.V c 1))) :=by
 let d:= daikon c
 let a:=P.oranges_hot x F sc seq d l v
 have j:d 3=0:=by simp [d,daikon,y.symm]
 have b:=P.oranges_splash x F sc seq d j (daiPen c) u
 rw [←daiV,sangre _ _ _ (show _ from j) zero_lt_one]
 simp only [Complex.ofReal_one]
 have t:= enters_all a b 1 (by change 0 < Complex.re _; simp)
 refine t.congr fun i=>?_
 simp only [Orange,Calvados,oceanRun,Complex.one_re,mul_one]
 rw [P.cider_true x F sc D n (seq i) (half_pos (P.jetS_pos _))]
#print axioms daiRise

/-- Strict UV spatial anisotropy obstacle. -/
lemma nougat:
 ∀ᶠ i in atTop,P.Calvados x sc seq (daikon 0) D i 1 ≠
      P.Calvados x sc seq (daikon 2) D i 1 :=by
 have y:= (P.daiRise x F sc seq D n l u v 0 (by decide)).sub
    (P.daiRise x F sc seq D n l u v 2 (by decide))
 exact (y.eventually_ne (sub_ne_zero.mpr (Gin.disc 1 zero_lt_one))).mono fun i j=>sub_ne_zero.mp j
#print axioms nougat

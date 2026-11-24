import Lucent.Atlas
import Lucent.Registry
import Lucent.Money
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

open Spine Preparation.Yoke Lucent EmberWind
variable (P:Spine)
local notation "Ξ" => household (P.calibration)
local notation "φ" => P.groundZero 3
local notation "Kₚ" => P.calibration

universe v0
variable {I:Type}[Fintype I]
variable {β:ℕ→ℝ}{R:ℕ→ℝ}{r:ℕ→ℕ}
variable {W:ℕ→I→Staff} {S:Stencil I} {m a:ℕ}{b:ℕ→ℕ}{d:FieldPlan I}
local notation:max "gong" => soundOf P β R W b S m a
local notation "mu" => P.pillars 3

open Preparation.Yoke.Lucent.Arity
structure Banner (I:Type)[Fintype I](P:Spine) where
    R:ℕ→ℝ
    r:ℕ→ℕ
    b:ℕ→ℕ
    W:ℕ→I→Staff
    plan:FieldPlan I
    u:I
    v:I
    i:I
    j:I
    k:I
    money:Money plan u v i j k
    bill:∃ B l, DanceCost B R W b l
    scale:MeasureAt plan W R r
    together:∀ᶠ s in atTop,(W s u).u=(W s v).u
    quick:Velocity P.par R r

#print Test
#check @riding
#check @qr_mul
variable (P: Spine)
section
variable (P:Spine)
 -- remove
example (F G:P.Test):P.Test:=F*G
end
import YM.SU5.SatinWard.Resolution.Tableyard
import YM.Mink.Geometry
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 8000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
open BProof Pressure
namespace Regulator

open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open _root_.YM.Regis.Head
open _root_.YM.Gleam.Luster.Almanac Grade
open _root_.YM.CF.Py.Rate.LocalLimit.Preparation _root_.YM.CF.Py.Rate.LocalLimit.Preparation.Tabletop Shrine Ione.Clock Moto
variable (P:Spine)
local notation "W★"=>P.calibration
local notation "Ω★"=>P.run.meter
open Preparation.Yoke Spine.Gingham Spine.Gingham.Diary
open ShapeLab ResolutionFrame Shrine 
open SatinWard
open Worth Pays BProof Aria Casting MacroGrid Selected OS.Semigroup OS.Semigroup.Marble PSE MarbleFace
open Internal
namespace Polaris
open Chili Rampart
variable (T:ℝ)(p:skit)(w:ℝ) (d:Rampart.Deck T p w) (t:0<T)
local notation "W" i:max=> closedBall (p i) w
abbrev physAnnot (x:Vantage) : E4:= WithLp.toLp 2 x
include d t
lemma vocation : ∀ x∈ closedBall (p false) w,∀ y∈closedBall (p true) w, 2*T< y 3-x 3 ∧ |y 3-x 3|+T < y 0-x 0∧ physAnnot y-physAnnot x∈ Mink.spacelike:=by
 intro x hx y hy; have h:=d x hx y hy; refine ⟨h.quest.1,h.wind,?_⟩; rw [Mink.lateral]; let z:= physAnnot y-physAnnot x; have M: |YM.time z|+T<y 0-x 0:=h.wind; let z':= YM.spatial z; have ht: |y 0-x 0|≤ ‖z'‖:= (show ‖z' (0:Fin 3)‖≤‖z'‖ from PiLp.norm_apply_le ..); exact (lt_trans (a:=|YM.time z|) (b:=|YM.time z|+T) (c:=y 0-x 0) (by linarith only [t]) M).trans_le ((le_abs_self (y 0-x 0)).trans ht)
lemma vocationDisjoint : Disjoint (closedBall (p false) w) (closedBall (p true) w):= by refine Set.disjoint_left.mpr ?_; intro x hx w; have h:= (vocation T p _ d t x hx x w).1; linarith
#print axioms vocation
end Polaris
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

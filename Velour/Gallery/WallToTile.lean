import Velour.Gallery.Slalom
import Velour.Messaline.Haute
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 1250000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set

open _root_.YM.SatinEdge.RealSheet Boundary Probe

open YM.Velour


variable (P:Spine)(a:P.Spectrum0 3)(j:Axis)
local notation "ξ"=> P.advocate 3 a j
local notation "S"=> P.seasons j ξ
local notation "Ω"=> P.heaven j ξ

variable {b:Axis}(J:P.Ellis 3 a)
include J
lemma jump_tile (h : j≠b) (r:P.JumpCard a j {OS.Semigroup.silk h}): Nonempty ((S).Tiles h):=
 let k:=(P.jumping a j J {OS.Semigroup.silk h}).mp r
 let v:=OS.Semigroup.silk h
 have d:v∈({v}:Set _) := rfl
 ⟨{
    cup:=fun u=> Celeritas.Division.cup (S) u k v d
    hol:=fun u _=> Celeritas.Division.cup_A (S) v u k d
    norm:=fun u z e=> Celeritas.Division.cupH (S) v u z k d e
    realC:=fun u l t=> Celeritas.Division.credit_h (S) v u t k d l
 }⟩
def Gymnasium : Prop:=
 ∀b:SpaceAxis,
   P.JumpCard a 3 {OS.Semigroup.silk (OS.Semigroup.royal b)} ∧
   P.JumpCard a (b.castSucc) {OS.Semigroup.silk (OS.Semigroup.royal b).symm}

theorem vault (h:P.Gymnasium a) : M4Furnish.Thirst P a:=by
 intro b
 obtain ⟨f,g⟩:=h b
 exact ⟨P.jump_tile a _ J _ f,P.jump_tile a _ J _ g⟩

#print axioms vault
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection


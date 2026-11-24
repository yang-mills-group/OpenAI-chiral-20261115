import Velour.Gallery.Drive
import Velour.Gallery.Motor
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

open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Celeritas.Division

variable (J:P.Ellis 3 a)(A:P.Apron)(v:OS.Cross j)(t:ℝ≥0)
local notation "y"=> ((t:ℝ) • v)
local notation "u" => ((1:ℝ≥0)+t)
local notation "C"=> P.slap a j A
local notation "E"=> (S).E
local notation "z"=> P.mounted j ξ A Ω

def jump (i:ℕ×ℕ):ℝ:=
 C 0 (u+u) i-2*C y (u+u) i-C 0 (1+1) i+2*C 0 (u+1) i
def score :ℝ:=
 dist ((S).U y (E u z)) (E u z)^2 - dist (E u z) (E 1 z)^2
include J
lemma jump_score :
 Tendsto (P.jump a j A v t) kindling (𝓝 (P.score a j A v t)):=by
 have d: 2 ≤ u+u:=one_add_one_eq_two (R:=ℝ≥0) ▸ add_le_add le_self_add le_self_add
 have e: 2 ≤ u+1:=by 
    rw [←one_add_one_eq_two]
    exact add_le_add_left le_self_add _
 rw [score,P.slide_spawn]


 exact (((P.slap_plate a j A 0 _ J d).sub
     ((P.slap_plate a j A y _ J d).const_mul 2)).sub
     (P.slap_plate a j A 0 _ J (le_of_eq one_add_one_eq_two.symm))).add
     ((P.slap_plate a j A 0 _ J e).const_mul 2)

def Stoppable :Prop:=
 ∀ε>0, ∀ᶠ i in kindling, P.jump a j A v t i < ε

lemma slalom2 :
 P.Stoppable a j A v t ↔
 dist ((S).U y (E u z)) (E u z) ≤ dist (E u z) (E 1 z) := by
 suffices e:P.Stoppable a j A v t ↔ P.score a j A v t ≤ 0 by
    rw [e,score,sub_nonpos, sq_le_sq₀ dist_nonneg dist_nonneg]
 constructor
 · intro h; by_contra! g
   obtain ⟨ε,l,r⟩:=exists_between g
   obtain ⟨i,p,m⟩:=((h ε l).and ((P.jump_score a j J A v t).eventually (lt_mem_nhds r))).exists
   exact (lt_asymm m p)
 intro d ε r
 exact (P.jump_score a j J A v t).eventually (gt_mem_nhds (d.trans_lt r))


def JumpCard (D:Set (OS.Cross j)) :Prop:=
 ∀ (A:P.Apron)(v:OS.Cross j), v∈D → ∀t:ℝ≥0, t ≤ 1 → P.Stoppable a j A v t

theorem jumping (D:Set (OS.Cross j)):
 P.JumpCard a j D ↔ Cinema (S) D:=by
 rw [_root_.YM.CF.Buffered.Afterglow.Hierarchy.Celeritas.Division.correct (S) D
          1 (show (0:ℝ)<1 by positivity) _ (P.sleeve_dense j ξ)]
 constructor
 · intro h _ e; obtain ⟨A,rfl⟩:=e; intro v g t l
   exact (P.slalom2 a j J A v t).mp (h A v g t (by exact_mod_cast l))
 intro h A v g t l
 exact (P.slalom2 a j J A v t).mpr (h (P.mounted j ξ A Ω) ⟨A,rfl⟩ v g t (by exact_mod_cast l))
#print axioms jumping
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection


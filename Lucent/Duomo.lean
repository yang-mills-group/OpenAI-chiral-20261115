import Lucent.Jackpot
import Lucent.Maple
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

open Ballad Arity Story
namespace Carillon
variable {a:ℝ}(e:0<a)

def basket (P:Spine){a:ℝ}(e:0<a):Banner (Fin 5) P where
 R:= framing (mosaic P.par a)
 r:= mosaic P.par a
 b:= arch (mosaic P.par a)
 W:= spell Story.points Story.arm song (mosaic P.par a)
 plan:= budget
 u:=0
 v:=1
 i:=2
 j:=3
 k:=4
 money:=link
 bill:=⟨_,_,chargeSpell P.par (fit _ e) Story.points Story.arm song (H:=2048) (by norm_num) tall Story.arms⟩
 scale:=measureSpell P.par (fit _ e) Story.points Story.arm song
 together:=Eventually.of_forall fun _=>rfl
 quick:=fit _ e

open Stationary (Gaia)
-- recognition from HoldRead at seats i, k
#check @PencilLease
#check @l_pt
#check @SitSpin.rest
#check @zoomR
#check @appoint_as


abbrev graph (P:Spine) (i:Fin 5):=gin (bar P.par • Story.points i)
abbrev dotsB (P:Spine)(a:ℝ)(i: Fin 5):= lime (Story.points i) ∘ Arity.mosaic P.par a

lemma pencilPine (i:Fin 5): 0<a → Appoint P.par a (dotsB P a i) (graph P i):= by
 intro t; apply (appoint_as _ t _ _).mpr
 refine (l_pt (bar P.par • Story.points i) (Velocity.normal P.par t)).congr fun s=> ?_
 unfold dotsB; rw [Function.comp_apply]; simp only [lime,smul_smul]; unfold Arity.mosaic; rw [mul_comm]

lemma orderGraph: (graph P 2) 2 < (graph P 4) 2 ∧ (graph P 2) 3 < (graph P 4) 3 :=by
 change (↑(bar P.par • (0:ℤ)):ℝ) < ↑(bar P.par • (2048:ℤ)) ∧ (↑(bar P.par • (0:ℤ)):ℝ)< ↑(bar P.par • (512:ℤ))
 have h:=barPos P.par; constructor <;> simp only [nsmul_eq_mul,mul_zero,Int.cast_zero] <;> positivity

lemma penLease : 0<a → PencilLease P a (graph P 2) (graph P 4) (dotsB P a 2) (dotsB P a 4):= fun p=>⟨pencilPine P _ p,pencilPine P _ p, fun q=> ((orderGraph P).1.ne (congrArg (fun z:Gaia=>z 2) q)).elim⟩

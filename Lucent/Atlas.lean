import Lucent.Uncouple
import Lucent.Swarm
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

theorem fullPoll (t:P.WickAtNative β) (v:Velocity P.par R r)(h:Whelk R r b W S m a d) (f:ℕ→P.Test)
     (e:∀ᶠ s in atTop, (f s).val=Ξ (gong s)):
   WakePoll P f (faq d S) := h.poll P t v ⟨wispFinal ..⟩ f e

def encode (F: Weaver):P.Test:= if h: TestFamily Kₚ true (Ξ F) then P.art (Ξ F) h else 0
lemma encode_wide {V F} (h:P.Wide F V): (P.encode F).val=Ξ F:= by rw [encode,dif_pos (aux_test h)]
abbrev rush(β R:ℕ→ℝ)(W:ℕ→I→Staff)(b:ℕ→ℕ)(S:Stencil I)(m a:ℕ):=fun s=>P.encode (soundOf P β R W b S m a s)
lemma rush_val (β:ℕ→ℝ)(h:Whelk R r b W S m a d):
   ∀ᶠ s in atTop,(P.rush β R W b S m a s).val= Ξ (soundOf P β R W b S m a s):= by
 obtain ⟨_,_,z⟩:=h.purse; exact (P.songrent (β:=β) (m:=m) (a:=a) (S:=S) z).mono fun _ e=>P.encode_wide e

theorem octavo(t:P.WickAtNative β)(v:Velocity P.par R r)(h:Whelk R r b W S m a d):
   WakePoll P (P.rush β R W b S m a) (faq d S):=P.fullPoll t v h _ (P.rush_val β h)
#check @QualifiedWakeReadout
#print axioms octavo

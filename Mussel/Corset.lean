import Mussel.Glade
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section

open Filter Function Set Metric MeasureTheory
open scoped Topology InnerProductSpace NNReal ComplexOrder BigOperators
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six
namespace Habitat
variable {P:Spine} {x:P.Spectrum0 3} {c r:ℕ→ℕ} {K:P.Register} {J:P.Ellis 3 x}
variable (B:P.Experiment K c r x J)(Z:Lead.Clan)
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "ω"=> P.colorZero 3 (P.otherSpectrum 3 3 x)
local notation "Ω"=> P.heaven 3 ξ
local notation "H"=> P.ManyF 3 ξ
local notation "G"=> P.ColorHil 3 (P.otherSpectrum 3 3 x)
namespace Hemlock
open PledgeT MiterT
open Broker
variable {s:ℕ}{f:P.Test}(F:Sentry P s f)(u:Vantage)(ε:ℝ)
local notation "τ"=>ruler P.par.block
/-- A clover operand *singly* clocked. physical center may be very far in the s grid but
must be close in time price to a point, already t>=0 birth. issued housing already at center. -/
structure Corset(A:Finset Cover): Prop where
 color : f∈enclave P.calibration
 book : f∈bay P.calibration A true
 whenZ : Between P.calibration 3 0 (τ* (F.w:ℤ)) A
 main_home :∀ y∈P.pinFoot s A,∀ j:Axis, |y j-u j|≤ε
 time_first : lane P s F.w ≤ε
 register : |u 3| ≤ ε

variable (A:Finset Cover)(Kz:Corset F u ε A)(t n:ℕ)
local notation "h0"=>lane P s F.w
local notation "j'"=>frost P s F.w u t
local notation "D"=> puppet P Z t n
local notation "W'"=>wing Z F t u n
local notation "Y"=> topArm (P:=P) (s:=s) t A
lemma marginW :0<h0:=when_pos _ s F.w F.ok -- coercions Real
lemma wing_home(v:s ≤ t){y:Vantage}(h:y ∈ P.pinFoot t W')(i:Axis):|y i-(P.meshPose t j') i| ≤ P.probeWidth t n i:=P.inside_now t j' D le_rfl h i
include Kz
lemma splitzone(v:s≤ t)(m:P.probeWidth t n 3<h0) : Disjoint (P.pinFoot t Y) (P.pinFoot t W') := by
 apply Set.disjoint_left.mpr; intro x p q
 have hu:= (span_lane P _ _ Kz.whenZ (P.pin_onward s t A v p)).2
 have hw:= abs_le.mp (wing_home Z F u t n v q 3)
 rw [snow] at hw
 · linarith
 exact v
lemma both_home (v:s≤ t)(a:pace P t ≤ ε)(p:∀ i:Axis,P.probeWidth t n i < h0){y:Vantage}(h:y∈P.pinFoot t (Y∪ W'))(j:Axis): |y j-u j|≤4*ε:=by
 have he:=Kz.time_first; have hv:=abs_le.mp Kz.register; specialize p j
 rw [P.pin_union] at h; rcases h with h|h
 · have hx:=abs_le.mp (Kz.main_home y (P.pin_onward s t A v h) j); rw [abs_le]; constructor <;>linarith
 have hx:= (abs_le.mp (wing_home Z F u t n v h j)); by_cases q:j=3
 · subst j; rw [snow _ _ _ _ _ v] at hx; rw [abs_le]; constructor <;>linarith
 have hf:= abs_le.mp (glaze P s F.w u t j q); rw [abs_le]; constructor <;>linarith
#print axioms both_home
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

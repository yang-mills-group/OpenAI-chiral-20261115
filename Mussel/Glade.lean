import Mussel.Safe
import Mussel.Prospect
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
variable {s:ℕ}{f:P.Test}(Kpp:Sentry P s f)(t:ℕ)(u:Vantage)(n:ℕ)
local notation "X"=>P.calibration
local notation "w"=>thickStep P s t Kpp.w
local notation "z"=> frost P s Kpp.w u t
local notation "A"=> P.conveying s (t-s) f
local notation "D"=> puppet P Z t n
local notation "C"=> P.issuing t D z
-- collar-splice on the CERT. equal to two histories (by def), then commute for all future.
lemma pointTail: ribbon Z t n z s Kpp=A*C:=by
 refine congrArg (A*·) ?_
 let z':= z; let W':=w; let F:=P.defaultR Z n; let G':=P.cruise (Vacancy.spare 3 (look 3)) z'; let L':=P.luggage 3 (look 3) (fun i=> z' i.val)
 rw [gossip_eq]; unfold collar gibbert; change _ = L' (P.shifts 3 (z' 3) (P.conveying t (t-t) (P.defaultR Z n))); rw [Nat.sub_self]; change P.shifts 3 ↑W' (L' (P.shifts 3 ↑W' F))= L' (P.shifts 3 (z' 3) F)
 have Jr(p:P.Test)(T:List (Trans (3:Axis))) : P.cruise (Vacancy.spare 3 T) z' p= P.luggage 3 T (fun i=> z' i.val) p:=by induction T with|nil=>rfl|cons i L h=> rw [P.ship_started,←h]; rfl
 unfold L'; rw [←Jr,←Jr,←P.cruise_mesh,P.shifts_sum,show z' 3=(W':ℤ)+W' from by change (if _ then (_:ℤ) else _)=(W':ℤ)+W';  dsimp only [W',thickStep]; simp only [if_true,Nat.cast_mul,Nat.cast_ofNat]; push_cast; ring]

noncomputable abbrev topArm(a':Finset Cover):Finset Cover:=volumeAround P.par P.width (t-s) a' -- A shadows notation!
-- supplies tape, sensing. key.Sandwich
abbrev wing := P.plotSet t D z
lemma tail_sensor (hn:P.calibration.ℓ<n): C∈ P.sensing (wing Z Kpp t u n) t Z.2:=by
 exact P.issuance_senses _ _ z D (Nat.le_refl _) (aware P Z t n hn)
def stage {a:Finset Cover}(p:f∈bay P.calibration a true)(b:f∈enclave P.calibration) (hn:P.calibration.ℓ<n)(h:Disjoint (P.pinFoot t (topArm (P:=P) (s:=s) t a)) (P.pinFoot t (wing Z Kpp t u n))):FrameZ P Z.2 t where
 mainStem:=A
 tailZ:=C
 S0:=topArm (P:=P) (s:=s) t a
 T0:=wing Z Kpp t u n
 mainPin:=(by exact (Tower.proceeds P.run P.large P.history.circuit s (t-s) ((Tapestry.locates ..).1 p)).1)
 mainColor:= P.refine_keeps _ _ b _
 tailPin:= P.issuing_support ..
 tailColor:=P.issuing_color t z D
 tailSense:=tail_sensor Z Kpp t u n hn
 clearF:=h
lemma rpc_stage {a:Finset Cover}(p:f∈bay P.calibration a true)(b:f∈enclave P.calibration) (hn:P.calibration.ℓ<n)(h:Disjoint (P.pinFoot t (topArm (P:=P) (s:=s) t a)) (P.pinFoot t (wing Z Kpp t u n))):(stage Z Kpp t u n p b hn h).question=ribbon Z t n z s Kpp:= (pointTail Z Kpp t u n).symm
end Hemlock
#print axioms Hemlock.stage
#print Hemlock.stage
#print axioms Hemlock.rpc_stage
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

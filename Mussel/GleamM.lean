import Mussel.Crash
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 800000
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
local notation "S"=>P.physicalEnergy 3 ξ
local notation "ν"=>P.shard x
variable {A C:P.Apron}(F R:SampleDose)(f:∀ y∈tsupport F.val, 0 ≤ y 3)(r':∀ y∈tsupport R.val, 0 ≤ y 3)
noncomputable def field(F:SampleDose)(q:P.birthF 3 A.s A.F):H := peg x (P.viewF 3 ξ A.s q) F
variable (x J)(D:P.Apron)(q1:P.birthF 3 A.s A.F)(q2:P.birthF 3 C.s C.F)
-- x explicit. field x args from notation (order x implicit)
#print field
include f J
lemma oneGlimpse : Tendsto (fun t:ℕ=> P.singleState 3 t x (P.prepared t A F)) atTop (𝓝 (inner ℂ Ω (field (x:=x) F q1))) :=by
 have h := spread (J:=J) F (P.viewF 3 ξ A.s q1)
 have hb : Tendsto (fun t=>inner ℂ ω (raySum x (P.viewF 3 ξ A.s q1) F t)) atTop (𝓝 (inner ℂ ω (P.enter 3 ξ (field (x:=x) F q1)))):= tendsto_const_nhds.inner h
 refine (show Tendsto (fun t=>inner ℂ ω (raySum x (P.viewF 3 ξ A.s q1) F t)) atTop (𝓝 (inner ℂ Ω (field (x:=x) F q1))) from hb).congr' ((eventually_ge_atTop A.s).mono fun t v=>?_)
 let he:=advanceW x A F q1 t f v; let b:=he.choose; have w:=he.choose_spec
 exact (congrArg (inner ℂ ω) w.symm).trans ((P.view_scalar 3 _ t b).trans (P.single_agrees 3 3 x t _))
include r'
lemma twoGlimpse : Tendsto (fun t:ℕ=> P.singleState 3 t x (P.reflectTest 3 (P.prepared t A F) * P.prepared t C R)) atTop (𝓝 (inner ℂ (field (x:=x) F q1) (field (x:=x) R q2))) :=by
 let l(A:P.Apron)(q:P.birthF 3 A.s A.F):= P.viewF 3 ξ A.s q
 have h:Tendsto (fun t=>inner ℂ (raySum x (l A q1) F t) (raySum x (l C q2) R t)) atTop (𝓝 (inner ℂ (field (x:=x) F q1) (field (x:=x) R q2))):= (spread (J:=J) F _).inner (spread (J:=J) R _)
 refine h.congr' ?_
 filter_upwards [eventually_ge_atTop A.s,eventually_ge_atTop C.s] with t v h'
 let hv:=advanceW x A F q1 t f v; let ht:=advanceW x C R q2 t r' h'; let a:=hv.choose; have w:=hv.choose_spec; let a':=ht.choose; have w':=ht.choose_spec
 exact (congrArg₂ (inner ℂ) w.symm w'.symm).trans ((P.released_gram 3 ξ t a a').trans (P.single_agrees 3 3 x t _))
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.Habitat.twoGlimpse

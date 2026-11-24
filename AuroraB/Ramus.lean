import AuroraB.TraceU
import AuroraB.Clockw
import AuroraB.Xphase
import SatinHeatSpecies
import AuroraB.Gill
import Mussel.Seal
import Mussel.Foil
import Mussel.Super
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
open PledgeT MiterT Broker
namespace AuroraB
open _root_.Yoland PledgeT MiterT Broker
open _root_.YM.Preen
variable {X:Hilbert}{j:Axis}(S:OS.Semigroup X j)(h:X)(e:‖h‖=1)(t:∀p:ℝ≥0,S.E p h=h)(i:ℕ)
include e t
lemma wall_z (x:X)(p:ℝ)(g:0<p)(v:0 < i): paster h (_root_.Yoland.pay S i p x)= _root_.Yoland.pay S i p x:=by
 have hx:=_root_.Yoland.turnΩ S x (paster h) (fun t' y=> (keep_heat h e S t t' y).symm) i g
 let T:=_root_.Yoland.pay S i p
 have he : T h=0:= keeps S h i g (fun _=>t _) v
 change paster h _= _; rw [hx,pasted _ e,map_sub,map_smul,he,smul_zero,sub_zero]
lemma flavor_z (x:X)(p:ℝ)(g:0<p)(v:0 < i): inner ℂ h (_root_.Yoland.pay S i p x)=0:=by
 let y:= _root_.Yoland.pay S i p x
 have h': paster h y=y:=wall_z S h e t i x p g v
 rw [pasted _ e, sub_eq_self] at h'
 exact (smul_eq_zero.mp h').resolve_right (norm_pos_iff.mp (by rw [e]; exact zero_lt_one))
omit e t
variable (d:ℕ)(C D:ℕ→ℕ→ℝ)(x)
lemma pretty_mean (n:ℕ)(q:0<n)(A:SampleDose): let Ω':=P.heaven 3 ξ; paster Ω' (beauty (P:=P) d C D (x:=x) n A)=beauty (P:=P) d C D (x:=x) n A∧ inner ℂ Ω' (beauty (P:=P) d C D (x:=x) n A)=0 :=by
 intro Ω'; let v:=P.seasons 3 ξ; exact ⟨wall_z v Ω' (stone_norm ..) (heaven_hot P 3 ξ) n _ _ (by exact_mod_cast q) q, flavor_z v Ω' (stone_norm ..) (heaven_hot P 3 ξ) n _ _ (by exact_mod_cast q) q⟩
#print axioms pretty_mean
end AuroraB
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

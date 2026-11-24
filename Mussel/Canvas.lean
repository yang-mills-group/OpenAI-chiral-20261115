import Mussel.Corset
import GlazeS.Licence
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
variable (P:Spine)(F:ℕ)(C D:ℕ→ℕ→ℝ)(s:ℕ)
local notation "a"=> Calico.bands (cellar P F s) 22
local notation "g"=>callix P F C D s
noncomputable abbrev durationZ (P:Spine)(s:ℕ):ℕ:=reachQ P s+22+P.calibration.ℓ+1
local notation "U"=> durationZ P s
local notation "R"=> ruler P.par.block
lemma dateZ :Between P.calibration 3 0 (R*U) a:=by
 intro q h
 let v:= nodeC (cellar P F s) 3
 obtain ⟨l,r⟩:= Calico.bands_spec _ h 3
 change - ((22:ℕ):ℤ) ≤ q 3-v at l; change q 3-v ≤ 22 at r
 have hh:=fresh P F s
 have ht:= (recess P F s).2
 change (_:ℤ)≤v at hh; change v≤ _ at ht
 have hn : ((reachQ P s+22+P.calibration.ℓ+1:ℕ):ℤ) ≤R*U:= le_mul_of_one_le_left (by positivity) (ruler_gene P.par.block)
 constructor <;>omega
def canvas: Sentry P s g where
 w:=U
 ok:= by unfold durationZ; omega
 pin:=by
    let Q:= P.positiveVox 3 s (a) (g) (programRent ..) (fun z t=> (dateZ P F s z t).1)
    refine ⟨Q,(a),?_,dateZ P F s⟩
    exact (Tapestry.locates ..).1 (programRent ..)
 val:=rfl
 care:=MiterT.pigment P F C D s
abbrev radius :ℝ:=lane P s U + intrinsic P s + tidal P F s
lemma radius_pos: 0 < Hemlock.radius P F s:= by
 have hv:= marginW (canvas P F (fun _ _=>0) (fun _ _=>0) s)
 have hx:= tide_price P F s
 have hr:0≤ intrinsic P s:=div_nonneg (by positivity) (mul_nonneg (by norm_num) (Tapestry.positiveScale P.par s).le)
 change 0<lane P s U at hv; unfold radius; linarith
lemma dressed : Corset (canvas P F C D s) (central P F s) (Hemlock.radius P F s) a:=by
 have hx:=tide_price P F s
 have hr:0≤ intrinsic P s:=div_nonneg (by positivity) (mul_nonneg (by norm_num) (Tapestry.positiveScale P.par s).le)
 have hb:=marginW (canvas P F C D s); change 0 < lane P s U at hb; unfold radius
 refine ⟨MiterT.pigment P F C D s, programRent .., dateZ P F s,fun y h j=>?_,?_,?_⟩
 · rw [abs_sub_comm]; exact (expense P _ s h j).trans (by linarith)
 · change lane P s U ≤_; linarith
 rw [MiterT.center3,abs_of_pos hx]; linarith
#print axioms dressed
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

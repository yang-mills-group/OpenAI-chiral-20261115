import Mussel.Corset
import Mussel.Supply
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
-- input.c,r Z ν x etc. choose once before test U F. stage titles not fixed explicitly? define
variable {s:ℕ}{f:P.Test}(F:Sentry P s f)(u:Vantage)(ε:ℝ)(A:Finset Cover)(Kz:Corset F u ε A)
structure Sewed(t n:ℕ) (D:FrameZ P Z.2 t)(a:P.birthF 3 t D.question) (x:P.Spectrum0 3): Prop where
 meter : s ≤ t
 instruction : D.question=ribbon Z t n (frost P s F.w u t) s F
 coordinates : ∀ i∈P.pinFoot t (D.S0∪D.T0), ∀ j:Axis, |i j-u j|≤4*ε
 arrive: ‖P.viewF 3 (P.otherSpectrum 3 3 x) t a-P.viewF 3 (P.otherSpectrum 3 3 x) s F.born‖ < ε
#print Sewed
variable (t n:ℕ)
local notation "Dg"=>Disjoint (P.pinFoot t (topArm (P:=P) (s:=s) t A)) (P.pinFoot t (wing Z F t u n))
include Kz
local notation "cT"=>frost P s F.w u t
lemma cooked (l:P.calibration.ℓ < n)(h:s ≤ t)(hi:Dg)(e:pace P t ≤ ε)(g:∀j:Axis,P.probeWidth t n j < lane P s F.w)
 (q : ‖P.viewF 3 ξ t (playClock Z t n cT s F h).born - F.beam ξ ω‖ < ε):∃ (D:FrameZ P Z.2 t)(a:P.birthF 3 t D.question),Sewed Z F u ε t n D a x:=by
 let T:=stage Z F t u n Kz.book Kz.color l hi
 have hx:T.question=ribbon Z t n cT s F:=rpc_stage ..
 let Q:= (playClock Z t n cT s F h).born; let a: P.birthF 3 t T.question:=(congrArg (P.birthF 3 t) hx).mpr Q
 have P':=P.identical_F 3 ξ t a Q hx
 let K'(x y:(G)):=‖x-y‖
 refine ⟨T,a,h,hx,?_,?_⟩
 · exact fun i p=> both_home Z F u ε A Kz t n h e g p
 exact lt_of_eq_of_lt (congrArg₂ K' P' (F.pays ξ F.born).symm) q

include B
lemma sew (l:0<ε):∃ i:ℕ,∃ (D:FrameZ P Z.2 (c i))(a:P.birthF 3 (c i) D.question),Sewed Z F u ε (c i) (r i) D a x:=by
 have p:= B.launch.smaller.tendsto_atTop
 have e:= B.launch.eager.tendsto_atTop
 let b:=lane P s F.w
 let T:=trans6 B; have hb:∀ᶠ i:ℕ in atTop,∀j:Axis,P.probeWidth (c i) (r i) j<b:= eventually_all.mpr fun i=>(T.widths i).eventually (gt_mem_nhds (marginW F))
 have hn : ∀ᶠ i:ℕ in atTop,P.calibration.ℓ< r i:= e.eventually (eventually_gt_atTop _)
 have hc:∀ᶠ i:ℕ in atTop,s ≤ c i:=p.eventually (eventually_ge_atTop _)
 have hv:∀ᶠ i:ℕ in atTop,pace P (c i) ≤ ε:= ((NNReal.tendsto_coe.mpr (MeshClock.vanishes (timeMesh P.par))).comp p).eventually (ge_mem_nhds l)
 have he:= ribbons_exposed B Z s F (fun i=>frost P s F.w u (c i)) hc ε l
 obtain ⟨i,h,n,z,m⟩:= (he.and (hb.and (hn.and hv))).exists
 obtain ⟨h1,h2⟩:=h
 exact ⟨i,cooked Z F u ε A Kz (c i) (r i) z h1 (splitzone Z F u ε A Kz (c i) _ h1 (n 3)) m n h2⟩
#print axioms sew
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

import Verts.Price
import Verts.PredictT
import AuroraB.Clot
import Minnow.Younger
import Acacia.Loom
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 470000
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
open PledgeT MiterT Broker Aloft
open Py.Rate.Pitching.Focus (Morn)
namespace AuroraB.Verts
open Calico _root_.Yoland
variable (d:ℕ)(C D:ℕ→ℕ→ℝ)
local notation "φ" s:max=> (P.macroStep s:ℂ)
local notation "χ" t:max=>P.singleState 3 t x
local notation "isp" v:max=>aislePt (3:Axis) v
local notation "kd" s:max=> offer_update P d C D s B Z
local notation "Τ" s:max => agent P d C D s B Z
local notation "X" s:max t:max n:max U:max=> schema B Z d C D s t n U
local notation "Ψ"=> P.seasons 3 ξ
local notation "Λ"=> P.wealth 3 ξ
open Py.Rate.Pitching.Focus MeasureTheory
-- readings assembled at fixed s,t in one P.elect.
variable (i:Lead.Clan)(w:ℝ)(s t n m:ℕ)(U V:SampleDose)
local notation "Y" s:max t:max=> schema B i d C D s t m V
local notation "aq" s:max t:max=> schema B Z d C D s t n U
local notation "R0"=>P.reflectTest 3
local notation "pL"=> fieldLimit x d C D n U
local notation "pR"=> fieldLimit x d C D m V
-- single w.A
variable (M:Morn P.par.K)(p:∀ s:ℕ,d ≤ s → Accordance P M d s (C s) (D s))(h:RobeRoad P d C D x)(e:0<w)(u:claimV w U)(v:claimV w V)
include B e u p h
#check @funded
lemma csu:Tendsto (fun s=>works B Z d C D s n U) atTop (𝓝 (pL)):=by
 let V:=funded B Z d C D w e n M p h
 obtain ⟨V₀,J,pe,hz,-,hx⟩:=V
 exact tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun s=>norm_nonneg _) (hx.mono fun _ hs =>hs U u) (by simpa using hz.const_mul (allowanceV U)))
set_option synthInstance.maxHeartbeats 280000 in
lemma embodied:Tendsto (fun s:ℕ=>limUnder atTop (fun t:ℕ=>absorb (x:=x) t (aq s t))) atTop (𝓝 (P.enter 3 ξ (pL))):=by
 have hp:=csu B Z d C D w n U M p h e u
 have hr:Continuous (fun z:(H)=>P.enter 3 ξ z):= by exact (P.enter 3 (P.otherSpectrum 3 3 x)).continuous
 exact (hr.continuousAt.tendsto.comp hp).congr' (((recessVanish P d).eventually (ge_mem_nhds e)).mono fun s k=>(sheen B Z d C D k U u n).limUnder_eq.symm)
-- exact convergence CP order.
structure Positions (f:ℂ)(a b:ℂ) : Prop where
 present:Tendsto (fun s:ℕ=> limUnder atTop (fun t=>(χ t) ((R0 (aq s t))*(Y s t)))) atTop (𝓝 f)
 gone:Tendsto (fun s:ℕ=> limUnder atTop (fun t=>(χ t) (R0 (aq s t)))) atTop (𝓝 a)
 turn:Tendsto (fun s:ℕ=> limUnder atTop (fun t=>(χ t) (Y s t))) atTop (𝓝 b)
include i v
lemma presented:Positions B Z d C D i n m U V (inner ℂ pL pR) (inner ℂ pL (Ω)) (inner ℂ (Ω) pR):=by
 let L(s:ℕ):=works B Z d C D s n U; let R(s:ℕ):=works B i d C D s m V
 have rL:= csu B Z d C D w n U M p h e u
 have rR:=csu B i d C D w m V M p h e v
 have he:∀ᶠ s:ℕ in atTop,tidal P d s ≤ w:= (recessVanish P d).eventually (ge_mem_nhds e)
 have hp(s:ℕ)(hs:tidal P d s ≤ w):= codaU B Z d C D s n m U V w u v i hs
 exact ⟨((rL.inner (𝕜:=ℂ) rR)).congr' (he.mono fun s k=>(hp _ k).1.limUnder_eq.symm), (show Tendsto (fun s=>inner ℂ (L s) (Ω)) atTop (𝓝 (inner ℂ pL (Ω))) from rL.inner tendsto_const_nhds).congr' (he.mono fun s k=> (hp _ k).2.1.limUnder_eq.symm), (show Tendsto (fun s=>inner ℂ (Ω) (R s)) atTop (𝓝 (inner ℂ (Ω) pR)) from tendsto_const_nhds.inner rR).congr' (he.mono fun s k=> (hp _ k).2.2.limUnder_eq.symm)⟩
#check @Spine.enter
#check @codaU
#check @csu
#print axioms presented
end AuroraB.Verts
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

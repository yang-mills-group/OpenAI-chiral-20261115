import Verts.Competence
import AuroraB.Clot
import Minnow.Younger
import Acacia.Loom
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 450000
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
variable(s t n m:ℕ)(U V:SampleDose)(w:ℝ)(e:0 < w)(u:claimV w U)(v:claimV w V)
variable (i:Lead.Clan)
local notation "Y" t:max=> schema B i d C D s t m V
local notation "aq" t:max=> schema B Z d C D s t n U
local notation "R0"=>P.reflectTest 3
include i u v B
lemma codaU(h:tidal P d s ≤ w):
 Tendsto (fun t=>(χ t) ((R0 (aq t))*(Y t))) atTop (𝓝 (inner ℂ (works B Z d C D s n U) (works B i d C D s m V)))∧
 Tendsto (fun t=>(χ t) (R0 (aq t))) atTop (𝓝 (inner ℂ (works B Z d C D s n U) (Ω))) ∧
 Tendsto (fun t=> (χ t) (Y t)) atTop (𝓝 (inner ℂ (Ω) (works B i d C D s m V))):=by
 let S(t:ℕ):= absorb (x:=x) t (aq t); let S'(t:ℕ):=absorb (x:=x) t (Y t)
 let y:= works B Z d C D s n U; let y':= works B i d C D s m V
 have hS:Tendsto S atTop (𝓝 (P.enter 3 ξ y)):= sheen B Z d C D h U u n
 have hT:Tendsto S' atTop (𝓝 (P.enter 3 ξ y')):= sheen B i d C D h V v m
 let k:=offer_update P d C D s B Z; let k':=offer_update P d C D s B i
 have hp:∀ᶠ t:ℕ in atTop,k ≤ t∧ k' ≤ t:=(eventually_ge_atTop k).and (eventually_ge_atTop k')
 let Gx:= fun t:ℕ=>inner ℂ (S t) (S' t)
 let xR:=fun t:ℕ=> inner ℂ (S t) (ω); let yS:=fun t:ℕ=>inner ℂ (ω) (S' t)
 have h₁:Tendsto Gx atTop (𝓝 (inner ℂ y y')):= hS.inner hT
 have h₂:Tendsto xR atTop (𝓝 (inner ℂ y (Ω))):= hS.inner tendsto_const_nhds
 have h₃:Tendsto yS atTop (𝓝 (inner ℂ (Ω) y')):= tendsto_const_nhds.inner hT
 have he:∀ᶠ t:ℕ in atTop,Gx t=(χ t) ((R0 (aq t))*(Y t))∧ xR t=(χ t) (R0 (aq t))∧yS t=(χ t) (Y t):=by
    filter_upwards [hp] with t ⟨k,k'⟩
    have a:=birth_schema B Z d C D k h U u n; have b:=birth_schema B i d C D k' h V v m
    have hF:S t=P.viewF 3 ξ t a:=BornAt (x:=x) a
    have hP:S' t=P.viewF 3 ξ t b:=BornAt (x:=x) b
    refine ⟨(congrArg₂ (inner ℂ) hF hP).trans ((P.released_gram 3 ξ t a b).trans (P.single_agrees 3 3 x t _)),?_,(congrArg (inner ℂ (ω)) hP).trans ((P.view_scalar 3 ξ t b).trans (P.single_agrees 3 3 x t _))⟩
    have hs:(inner ℂ (ω) (S t))=(χ t) (aq t):=(congrArg (inner ℂ (ω)) hF).trans ((P.view_scalar 3 ξ t a).trans (P.single_agrees 3 3 x t _))
    let r:= (χ t)
    exact Eq.trans (inner_conj_symm (𝕜:=ℂ) (S t) (ω)).symm ((congrArg (starRingEnd ℂ) hs).trans (P.opposed_single x t (aq t)).symm)
 exact ⟨h₁.congr' (he.mono (fun t p=>p.1)),h₂.congr' (he.mono (fun t p=>p.2.1)), h₃.congr' (he.mono (fun t p=>p.2.2))⟩
#check @opposed_single
#print axioms codaU
end AuroraB.Verts
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

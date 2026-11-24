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
attribute [local instance] InnerProductSpace.complexToReal
open _root_.YM.Preen DoseTravel
variable (x) (j:ℕ)(y:P.ManyF 3 (P.otherSpectrum 3 3 x))(v:PeriodS P d C D x j y)
local notation "θ"=>tidal P d j
local notation "Q"=> MiterT.pointT P d C D ξ
local notation "p0"=>crest P d
local notation "T"=>P.cartage 3 ξ
noncomputable def zoomV (m:ℕ)(q:Vantage): H:= iteratedDeriv m (fun t:ℝ=> Q (q+aislePt (3:Axis) t)) 0
include v
private lemma resolutionV (a:Vantage)(p:θ<a 3)(t:ℝ)(u:θ<a 3 + t):
 Q (a+aislePt (3:Axis) t)= T (a-p0) (dawn (Ψ) (a 3-θ+t) y):=by
 let z:=isp t
 have he:(a+z) 3=a 3+t:=by rw [Pi.add_apply,show z 3=aislePt 3 t 3 from rfl,location₁]
 have hp:= v.2 (a+z) (he.symm ▸ u)
 have h': (a+z)-p0=(a-p0)+isp t:=by unfold z; ext; simp; ring
 have hc':T (a+z-p0)=T (a-p0):=(congrArg (T) h').trans (caesium x (a-p0) t)
 have h₁:(a+z) 3-θ=a 3-θ+t:=by rw [he]; ring
 exact Eq.trans hp (congrArg₂ (fun (g:(H).Op) (t:ℝ)=>g ((Ψ).E t.toNNReal y)) hc' h₁)
set_option maxHeartbeats 870000 in
lemma dot_port(m:ℕ)(q:Vantage)(e:θ<q 3):zoomV x d C D m q=T (q-p0) (_root_.Yoland.pay (Ψ) m (q 3-θ) y):=by -- order parameters x maybe #check
 let t₀:ℝ:=q 3-θ; let g(r:ℝ):=(dawn (Ψ) (t₀+r))
 let J:=T (q-p0); let Y:= (J.comp (ContinuousLinearMap.apply ℂ _ y)).restrictScalars ℝ -- apply source H.Op maybe implicit.
 have H0:0<t₀:= sub_pos.mpr e
 have ht: (fun t:ℝ=>Q (q+isp t)) =ᶠ[𝓝 (0:ℝ)] (Y ∘ g):=by
    filter_upwards [lt_mem_nhds (neg_lt_zero.mpr H0)] with v' b
    exact resolutionV x d C D j y v _ e v' (by unfold t₀ at b; linarith)
 have e0:AnalyticAt ℝ g 0:= ((dawnRise (Ψ) _ (show 0<t₀+0 from by rw [add_zero]; exact H0)).comp (analyticAt_const.add analyticAt_id))
 exact (ht.iteratedDeriv_eq m).trans ((transport e0 Y m).trans (congrArg Y (show iteratedDeriv m g 0=_root_.Yoland.pay (Ψ) m t₀ from by unfold g; simp only [iteratedDeriv_comp_const_add,add_zero])))
noncomputable def fieldLimit(m:ℕ)(A:SampleDose):H:=∫ z:Vantage,(A.val z:ℂ) • zoomV x d C D m z
variable (U:SampleDose)(w:ℝ)(h:∀ i∈tsupport U.val,w < i 3)(l:tidal P d j < w)
local notation "assetT" m:max t:max=> _root_.Yoland.pay (Ψ) m t
include h l
lemma volley (m:ℕ)(q:Vantage)(p:q∈tsupport U.val): let k:=q 3- w; zoomV x d C D m q=(assetT m (w-θ)) (T (q-p0) (dawn (Ψ) k y)):=by
 intro k; have hv:=h _ p
 let a:=w-θ; have ha:0<a:=sub_pos.mpr l; have hb:0<k:=sub_pos.mpr hv

 let g:=T (q-p0)
 -- turnΩ recv cart commutes
 refine Eq.trans (dot_port x d C D j y v m q (l.trans hv)) (Eq.trans (congrArg (fun t:ℝ=>g ((assetT m t) y)) (show q 3-θ=a+k from by unfold a k; ring)) ?_)
 exact Eq.trans (congrArg g (growJet (Ψ) y m hb ha).symm) (_root_.Yoland.turnΩ (Ψ) (dawn (Ψ) k y) g (fun t z=>(P.warm_drive 3 ξ (q-p0) t z).symm) m ha)
#print zoomV
#check @growJet
#print axioms volley
end AuroraB.Verts
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

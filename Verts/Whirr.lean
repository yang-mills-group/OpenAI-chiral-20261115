import Verts.Born
import Minnow.Front
import AuroraB.Clot
import Minnow.Younger
import Acacia.Loom
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
open _root_.YM.Preen DoseTravel _root_.Acacia
local notation "incomeQ" s:max m:max=>_root_.Yoland.frame (Ψ) m (P.macroStep s) (ContinuousLinearMap.id ℂ (H).space)
variable(s n:ℕ)(w:ℝ)(k:tidal P d s ≤ w)(U:SampleDose)(p:claimV w U)
include k p
-- general crypto.
private lemma rain (r:ℝ)(v:0 ≤r): vistaH B Z d C D s (shuf U r)=dawn (Ψ) r (vistaH B Z d C D s U):= apronShift x (kd s) r v _ U (central P d s) ( Invor d U p s k)
lemma cost_w : works B Z d C D s n U=(incomeQ s n) (vistaH B Z d C D s U):=by
 let S:=Ψ; let r:=P.macroStep s
 let F:=ContinuousLinearMap.id ℂ (H).space
 let Y(i):=_root_.Yoland.frame S i r F
 let f(U:SampleDose):=vistaH B Z d C D s U
 induction n generalizing U with
 | zero=>rfl
 | succ n ih=>
    let z:=shuf U r
    have e:= Shuffled U p r (P.macroStep_pos s).le
    let k':=f U; let z':= ((φ s)⁻¹:ℂ)
    have hw: z' • (f z-f U)=noon S r (f U):= pager (R:=H) S k' (f z) r (rain B Z d C D s w k U p r (P.macroStep_pos s).le)
    let b:= works B Z d C D s n
    have hx := congrArg₂ (fun v e:(H)=> z' • (v-e)) (ih z e) (ih U p)
    exact (rStorm B d C D s U n Z).trans (hx.trans ((mapDiff _ hw).trans (motiveV (R:=H) S n r _)))
where pager{R:Hilbert}(S:OS.Semigroup R (3:Axis))(a b:R)(r:ℝ)(h:b=dawn S r a):((r:ℂ)⁻¹:ℂ) •(b-a)=noon S r a:=by change _=r⁻¹ • (dawn S r a-a); rw [←Complex.ofReal_inv,Complex.coe_smul,h]
      mapDiff{R:Hilbert}(D:R.Op){x y z:R}{k:ℂ}(h:k •(x-y)=z):k •(D x-D y)=D z:=by rw [←map_sub,←map_smul,h]
      motiveV{R:Hilbert}(S:OS.Semigroup R (3:Axis))(n:ℕ)(r:ℝ)(z:R): let i:=ContinuousLinearMap.id ℂ R.space; frame S n r i (noon S r z)=frame S (n+1) r i z:=by
        intro i; induction n with|zero=>rfl|succ n ih=> exact congrArg (fun y:R=>noon S r y) ih
#print axioms cost_w
lemma charged_pay(e:ℝ)(h:0 ≤ e)(q:claimV (w+e) U) : works B Z d C D s n U= _root_.Yoland.frame (Ψ) n (P.macroStep s) (_root_.Yoland.dawn (Ψ) e) (vistaH B Z d C D s (shuf U (-e))):=by
 let g:=shuf U (-e)
 have he:claimV w g:=by intro i b; have h:=q _ ((shuf_iff ..).mp b); rw [Pi.sub_apply,location₁] at h; linarith
 have hp:=rain B Z d C D s w k g he e h
 have hd:shuf g e=U:=by unfold g; rw [shuf_add,neg_add_cancel,shuf_base]
 let D₀:=vistaH B Z d C D s
 let S:=Ψ; let t:=P.macroStep s
 have hy:D₀ U=dawn S e (D₀ g):= (congrArg D₀ hd).symm.trans hp
 exact Eq.trans (cost_w B Z d C D s n w k U p) (op_launch (R:=(H)) S hy t e n) -- order t before e? e known by proof. helper
where op_launch{R:Hilbert}(S:OS.Semigroup R (3:Axis)){e:ℝ}{x y:R}(h:x=dawn S e y)(t e':ℝ)(n:ℕ):frame S n t (ContinuousLinearMap.id ℂ R.space) x= frame S n t (dawn S e) y:= by
       let I:=ContinuousLinearMap.id ℂ R.space; change frame S n t I x=_; rw [show dawn S e=I.comp (dawn S e) from rfl,framed]
       exact congrArg _ h
#print axioms charged_pay
end AuroraB.Verts
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

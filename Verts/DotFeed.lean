import Verts.Forte
import Verts.Dot
import Verts.Born
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
open _root_.YM.Preen DoseTravel
variable (x) (j:ℕ)(y:P.ManyF 3 (P.otherSpectrum 3 3 x))(v:PeriodS P d C D x j y)(U:SampleDose)(w:ℝ)(h:claimV w U)(l:tidal P d j < w)
local notation "θ"=>tidal P d j
local notation "Q"=> MiterT.pointT P d C D ξ
local notation "p0"=>crest P d
local notation "T"=>P.cartage 3 ξ
local notation "YQ"=> tempoV x d y w
local notation "bill" m:max t:max=> _root_.Yoland.pay (Ψ) m t
include v l h
#check @volley
lemma smearV(m:ℕ)(i:Vantage): (U.val i:ℂ) • zoomV x d C D m i=(bill m (w-θ)) ((U.val i:ℂ) • YQ i):=by
 by_cases e:U.val i=0
 · exact null_point (R:= (H)) _ _ _ (show (U.val i:ℂ)=0 from Complex.ofReal_eq_zero.mpr e)
 exact paid_point (R:= (H)) _ _ ((U.val i):ℂ) _ (volley x d C D j y v U w h l m i (subset_closure e))
where null_point {R:Hilbert}(a b:R)(f:R.Op){z:ℂ}(h:z=0): z • a=f (z • b):=by simp only [h,zero_smul,map_zero]
      paid_point {R:Hilbert}(a b:R)(z:ℂ)(f:R.Op)(h:a=f b): z • a=f (z • b):=by rw [h,map_smul]
lemma accept : Integrable (fun i:Vantage => (U.val i:ℂ) • YQ i):= weightedMoney U _ _ (tempoFeed x d _ w)
lemma financed(m:ℕ) : fieldLimit x d C D m U=(bill m (w-θ)) (∫ i:Vantage,(U.val i:ℂ) • YQ i):=by
 let f(i:Vantage):=(U.val i:ℂ) • YQ i
 apply Eq.trans (integral_congr_ae (Eventually.of_forall (smearV x d C D j y v U w h l m)))
 exact ContinuousLinearMap.integral_comp_comm _ (accept x d C D j y v U w h l)
lemma integrationV(m:ℕ) : Integrable (fun i:Vantage=>(U.val i:ℂ) • zoomV x d C D m i):= ((bill m (w-θ)).integrable_comp (accept x d C D j y v U w h l)).congr (Eventually.of_forall (fun q:Vantage=>(smearV x d C D j y v U w h l m q).symm))
lemma translate {r:ℝ}(p:r=w-θ):let V:=shuf U (-r); MiterT.cloud P d C D x V= ∫ i:Vantage,(U.val i:ℂ) • YQ i:=by
 intro V
 have hp:claimV θ V:=by
    intro i hk; have e:=h _ ((shuf_iff ..).mp hk); rw [Pi.sub_apply,location₁] at e
    rw [p] at e; linarith only [e]
 let t:= (isp (-r)); let f(i:Vantage):=(V.val i:ℂ) • tempoV x d y (θ) i
 refine Eq.trans (cloud_exact x d C D j y v V hp) (Eq.trans (integral_add_right_eq_self f t).symm (integral_congr_ae (Eventually.of_forall fun i=>?_)))
 have he:(V.val (i+t):ℂ)=(U.val i:ℂ):=congrArg (fun q:Vantage=>(U.val q:ℂ)) (add_neg_cancel_right i t)
 have hc : T (i+t-p0)=T (i-p0):=(congrArg (T) (show i+t-p0=(i-p0)+isp (-r) from by unfold t; ext; simp; ring)).trans (caesium x (i-p0) (-r))
 have ht : (i+t) 3 - θ=i 3 - w :=by rw [Pi.add_apply,show t 3= -r from location₁ _,p]; ring
 exact congrArg₂ (fun (l:ℂ) (f:(H).space)=>l • f) he (congrArg₂ (fun (g:(H).Op) (t:ℝ)=>g ((Ψ).E t.toNNReal y)) hc ht)
#print axioms translate
#print axioms integrationV
end AuroraB.Verts
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

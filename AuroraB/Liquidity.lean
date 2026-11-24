import AuroraB.Peakw
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
open _root_.Yoland Py.Rate.Pitching.Focus PledgeT MiterT Aloft DoseTravel Calico
open _root_.YM.Preen
local notation "ι"=>(3:Axis)
local notation "Ψ"=> P.seasons 3 ξ
local notation "Λz"=> P.cartage 3 ξ
local notation "pr"=>paster (Ω)
variable (x)(d:ℕ)(C D:ℕ→ℕ→ℝ)(j:ℕ)(y:(P.ManyF 3 (P.otherSpectrum 3 3 x)).space)(hY:PeriodS P d C D x j y)
local notation "hr"=>tidal P d j
local notation "c0"=>crest P d
local notation "ημ"=> _root_.Yoland.pay
abbrev PA(U:SampleDose): Prop:=∀t∈tsupport U.val, max ((core:ℝ)+1) ((core:ℝ)+(hr)) < t 3
variable (A:SampleDose)(pA:PA (P:=P) d j A)
local notation "zQz"=>fun z:Vantage=>Λz (z-c0) (dawn (Ψ) (z 3-hr) y)
private lemma flour(z:Vantage)(a:ℝ): Λz ((z-aislePt 3 a)-c0)=Λz (z-c0):=by
 have he:(z-aislePt 3 a)-c0=(z-c0)+aislePt 3 (-a):=by
    funext i; by_cases p:i=3<;> simp only [Pi.sub_apply,Pi.add_apply, location,p,↓reduceIte]; ring
    ring
 exact (congrArg ((P.cartage 3 ξ)) he).trans (caesium x (z-c0) (-a))
include hY
private lemma energy_true (V:SampleDose)(g:∀t∈tsupport V.val, tidal P d j<t 3): MiterT.cloud P d C D x V=DoseTravel.beam (P.ManyF 3 (P.otherSpectrum 3 3 x)) V (zQz):=by
 unfold MiterT.cloud DoseTravel.beam actualThinR; apply integral_congr_ae; filter_upwards with t
 by_cases h:V.val t=0; · simp only [h,Complex.ofReal_zero,zero_smul]
 exact congrArg (fun k:(H)=> (V.val t:ℂ) • k) (hY.2 t (g t (subset_closure h)))
omit hY
private lemma shaped(t:Vantage)(i:Lead.Clan): shapeΨ x d j y i t=(ημ) (Ψ) (score i) (score i) ((zQz) (t-aislePt 3 (score i))):=by
    let v:= aislePt 3 (score i)
    exact strain (R:=H) ((ημ) (Ψ) (score i) (score i)) y (dawn (Ψ)) (flour x d t (score i)) (a:=t 3-(score i:ℝ)-hr) (b:= (t-v) 3-hr) (congrArg (fun z:ℝ=>(t 3-z)-hr) (location₁ (score i)).symm)
where strain {R:Hilbert}(X:R.Op)(y:R)(f:ℝ→R.Op){A Gx:R.Op}(e:Gx=A){a b:ℝ}(v:a=b): X (A (f a y))=X (Gx (f b y)):=by rw [e,v]
include hY pA
set_option maxHeartbeats 450000 in
lemma canny(i:Lead.Clan): beauty d C D (x:=x) (score i) A=DoseTravel.beam (H) A (shapeΨ x d j y i):=by
 let n:ℕ:=score i
 let V:= shuf A (-(n:ℝ))
 let v:=aislePt 3 (n:ℝ)
 have hx:0<(n:ℝ):=by exact_mod_cast (scoring i).1
 have hb : (n:ℝ) ≤ core:= by exact_mod_cast (scoring i).2
 have g : ∀t∈ tsupport V.val, hr < t 3:= by
    intro t h; have hp:=pA _ ((shuf_iff ..).mp h); rw [Pi.sub_apply,location₁] at hp; linarith only [hp,hb,le_max_right ((core:ℝ)+1) ((core:ℝ)+(hr))]
 let zK:= zQz
 have hz:MiterT.cloud P d C D x V=DoseTravel.beam (H) V zK:= energy_true x d C D j y hY V g
 let T:= (ημ) (Ψ) n (n:ℝ)
 change T (MiterT.cloud P d C D x V)=_
 refine (congrArg (fun b:(H)=> T b) hz).trans ?_
 have he:Continuous zK:= P.caravan 3 ξ (fun t=>t-crest P d) _ (continuous_id.sub continuous_const) (((Ψ).continuousE _).comp (by fun_prop))
 have hF(t:Vantage): V.val (t-v)=A.val t:=by
    have hi:t-v + -aislePt 3 (-(n:ℝ))=t:=by funext j; by_cases p:j=3 <;> simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,v,location,p,↓reduceIte]; ring; ring
    exact congrArg A.val hi
 have hs(t:Vantage) : shapeΨ x d j y i t=T (zK (t-v)):=shaped x d j y t i
 exact reins (R:=H) zK T he V A v hF _ hs
where reins{R:Hilbert}(f:Vantage→R)(T:R.Op)(p:Continuous f)(V A:SampleDose)(v:Vantage)(hV:∀t,V.val (t-v)=A.val t)(g:Vantage→R)(hg:∀ t,g t=T (f (t-v))):T (DoseTravel.beam R V f)=DoseTravel.beam R A g:=by
        have he:=weightedMoney V R f p
        unfold DoseTravel.beam; rw [← ContinuousLinearMap.integral_comp_comm _ he,← integral_add_right_eq_self (fun z:Vantage=>T ((V.val z:ℂ) • f z)) (-v)]
        apply integral_congr_ae; filter_upwards with z; rw [← sub_eq_add_neg,hV,hg,map_smul]
#print axioms canny
end AuroraB
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

import Minnow.Cart
import AuroraB.Clot
import HectorA.Iota
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
open PledgeT MiterT Broker
open _root_.Yoland Py.Rate.Pitching.Focus Calico DoseTravel
open _root_.YM.Preen MiterT.Mido
variable(F:ℕ)(C D:ℕ→ℕ→ℝ)(M:Morn P.par.K)(hM:∀i:ℕ,F ≤ i → Accordance P M F i (C i) (D i))(hq:RobeRoad P F C D x)(A:SampleDose)(d:ℝ)
local notation "S"=>P.seasons 3 ξ
local notation "U"=>P.cartage 3 ξ
local notation "Π"=>P.wealth 3 ξ
local notation "c0"=> crest P F
local notation "fu"=> _root_.Yoland.pay
variable (x)(j:ℕ)(y:(P.ManyF 3 (P.otherSpectrum 3 3 x)).space)
noncomputable def prettyR (i:Lead.Clan) : H:= (fu) (S) (score i) d (MiterT.cloud P F C D x (shuf A (-d)))
noncomputable def lister (i:Lead.Clan)(p:Vantage): H:= (fu) (S) (score i) d (U (p-c0) (_root_.Yoland.dawn (S) (p 3-d-tidal P F j) y))
lemma listerC(i:Lead.Clan): Continuous (lister x F d j y i):=(( (fu) (S) (score i) d)).continuous.comp (P.caravan 3 ξ (fun t=>t-c0) (fun p:Vantage=> (S).E ((p 3-d-tidal P F j).toNNReal) y) (continuous_id.sub continuous_const) (((S).continuousE _).comp (by fun_prop))) -- lambda y infer?
lemma lister_at (i: Lead.Clan)(t:Vantage)(p:0<d)(h:d+tidal P F j < t 3): lister x F d j y i t=noferal P x F j y t i:=by
 let T':=U (t-c0); let a:= (t 3-d-tidal P F j); let q:=score i; let T:=S
 have hx₀:0<a:=by unfold a; linarith only [h]
 exact powerUp (R:=H) y a (t 3-tidal P F j) q T T' (by unfold a; ring) hx₀ p (fun r y=>(P.warm_drive 3 ξ (t-c0) r y).symm)
where powerUp{R:Hilbert}(y:R)(a b:ℝ)(i:ℕ)(T:OS.Semigroup R (3:Axis))(Z:R.Op){d:ℝ}(he:d+a=b)(ha:0<a)(hb:0<d)(hu:∀r y,Z (T.E r y)=T.E r (Z y)): _root_.Yoland.pay T i d (Z (dawn T a y))=Z (_root_.Yoland.pay T i b y):=by rw [← _root_.Yoland.turnΩ T _ Z hu _ hb, growJet T y _ ha hb,he]
variable(p:0<d)(hrP:Aloft.PeriodS P F C D x j y)(g:∀ t∈tsupport A.val,d+tidal P F j<t 3)
include p hrP g
set_option maxHeartbeats 535000 in
lemma drawn (i:Lead.Clan): prettyR x F C D A d i= DoseTravel.beam (H) A (lister x F d j y i):=by
 let q:=shuf A (-d); let v':= aislePt 3 d
 let f(z:Vantage):=U (z-c0) (dawn (S) (z 3-tidal P F j) y)
 have hp:∀ z∈ tsupport q.val,tidal P F j<z 3:=by
    intro z t; have he:=g _ ((shuf_iff ..).mp t); rw [Pi.sub_apply,location₁] at he; linarith only [he]
 have hz:MiterT.cloud P F C D x q=DoseTravel.beam (H) q f:=by
    unfold MiterT.cloud DoseTravel.beam actualThinR; apply integral_congr_ae; filter_upwards with t
    by_cases h:q.val t=0; · simp only [h,Complex.ofReal_zero,zero_smul]
    exact congrArg (fun k:(H)=> (q.val t:ℂ) • k) (hrP.2 t (hp t (subset_closure h)))
 let T:= (fu) (S) (score i) d
 change T _=_; refine (congrArg (fun b:(H)=> T b) hz).trans ?_
 have he:Continuous f:= P.caravan 3 ξ (fun z=>z-crest P F) (fun p:Vantage=>(S).E ((p 3-tidal P F j).toNNReal) y) (continuous_id.sub continuous_const) (((S).continuousE _).comp (by fun_prop))
 have hF(t:Vantage): q.val (t-v')=A.val t:=by
    have hi:t-v' + -aislePt 3 (-d)=t:=by funext j; by_cases p:j=3 <;> simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,v',location,p,↓reduceIte]; ring; ring
    exact congrArg A.val hi
 have hs(t:Vantage) : lister x F d j y i t=T (f (t-v')):=by
    have ht:(t-v'-c0)=(t-c0)+aislePt 3 (-d):=by funext j; unfold v'; by_cases q:j=3<;> simp only [Pi.add_apply,Pi.sub_apply,location,q,↓reduceIte];ring;ring
    have hw:U (t-v'-c0)=U (t-c0):= (congrArg (P.cartage 3 ξ) ht).trans (caesium x (t-c0) (-d))
    exact congrArg₂ (fun (u:(H).Op)(z:ℝ)=>T (u (dawn (S) z y))) hw.symm (show t 3-d-tidal P F j=(t-v') 3-tidal P F j from congrArg (fun d:ℝ=> t 3-d-tidal P F j) (location₁ _).symm)
 exact reins (R:=H) f T he q A v' hF _ hs
where
 reins{R:Hilbert}(f:Vantage→ R)(T:R.Op)(p:Continuous f)(V A:SampleDose)(v:Vantage)(hV:∀t,V.val (t-v)=A.val t)(g:Vantage→R)(hg:∀ t,g t=T (f (t-v))):T (DoseTravel.beam R V f)=DoseTravel.beam R A g:=by have he:=weightedMoney V R f p; unfold DoseTravel.beam; rw [← ContinuousLinearMap.integral_comp_comm _ he,← integral_add_right_eq_self (fun z:Vantage=>T ((V.val z:ℂ) • f z)) (-v)]; apply integral_congr_ae; filter_upwards with z; rw [← sub_eq_add_neg,hV,hg,map_smul]
#print axioms drawn
#print axioms listerC
end AuroraB
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

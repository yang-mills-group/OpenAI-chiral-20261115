import HectorA.Iota
import AuroraB.Viaduct
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
set_option maxHeartbeats 500000
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
open PledgeT MiterT Aloft _root_.Yoland DoseTravel Py.Rate.Pitching.Focus
open _root_.YM.Preen
local notation "ι"=>(3:Axis)
local notation "Ψ"=> P.seasons 3 ξ
local notation "Λz"=> P.cartage 3 ξ
local notation "pr"=>paster (Ω)
abbrev core : ℕ:=Fintype.card Lead.Clan
abbrev mission : Lead.Clan≃Fin core := Fintype.equivFin Lead.Clan
abbrev score(i:Lead.Clan):ℕ:=(mission i).val+1
lemma scoring(i:Lead.Clan):1 ≤ score i ∧ score i ≤ core:= ⟨Nat.le_add_left _ _,(mission i).isLt⟩
-- use actual a, @ y provided and t>max.J.S.K. need cast pay map inner. no local Real instance.One.P.En.P.
variable (x)(d:ℕ)(C D:ℕ→ℕ→ℝ)(j:ℕ)(y:(P.ManyF 3 (P.otherSpectrum 3 3 x)).space)(hY:PeriodS P d C D x j y)(q:¬FiniteDimensional ℂ (asset P x (paster (P.heaven 3 (P.otherSpectrum 3 3 x)) y)))
local notation "hr"=>tidal P d j
local notation "c0"=>crest P d
local notation "ιy"=> pr y
-- Continuous surrogate extends at cutoff layer hr+n ticks.For deriving next.
noncomputable def shapeΨ(i:Lead.Clan)(t:Vantage):H:=let n:ℝ:= score i; let z:=Λz (t-c0);  _root_.Yoland.pay (Ψ) (score i) n (z (dawn (Ψ) (t 3-n-hr) y))
-- yr.Support.Virtual.S vs actual. $
lemma shapeC(i:Lead.Clan):Continuous (shapeΨ x d j y i):=by
 let n:ℝ:=score i
 exact (( _root_.Yoland.pay (Ψ) (score i) n)).continuous.comp (P.caravan 3 ξ (fun t=>t-c0) (fun t:Vantage=>(Ψ).E (t 3-n-hr).toNNReal y) (continuous_id.sub continuous_const) (((Ψ).continuousE _).comp (by fun_prop)))
lemma shapeAt (i: Lead.Clan)(t:Vantage) (h:(score i:ℝ)+(hr) < t 3): shapeΨ x d j y i t= Λz (t-c0) ( _root_.Yoland.pay (Ψ) (score i) (t 3-hr) y):=by
 let P':=Λz (t-c0); let a:= (t 3-(score i:ℝ)-(hr)); let S:=Ψ; let n:=score i
 have hp:0<(score i:ℝ):=by exact_mod_cast (scoring i).1
 have hx₀:0<a:=by unfold a; linarith only [h]
 exact powerUp (R:=H) y a (t 3-hr) n S P' (by unfold n a; ring) hx₀ hp (fun r y=>(P.warm_drive 3 ξ (t-c0) r y).symm)
where powerUp{R:Hilbert}(y:R)(a b:ℝ)(i:ℕ)(S:OS.Semigroup R (3:Axis))(U:R.Op)(he:(i:ℝ)+a=b)(ha:0<a)(hb:0<(i:ℝ))(hu:∀r y,U (S.E r y)=S.E r (U y)): _root_.Yoland.pay S i i (U (dawn S a y))=U (_root_.Yoland.pay S i b y):=by rw [← _root_.Yoland.turnΩ S _ U hu _ hb, growJet S y _ ha hb,he]
include q
lemma shapeLive(t:Vantage)(h:(core:ℝ)+(hr)<t 3): LinearIndependent ℂ (fun i:Lead.Clan=> pr (shapeΨ x d j y i t)):=by
 let z:=ιy; let S:= Ψ; let V:= Λz (t-c0); let b:= t 3-hr
 have hg:0<b:=by unfold b; linarith only [show 0 ≤ (core:ℝ) from (by positivity),h]
 let f(i:Lead.Clan):= detail S z (score i) b
 have H': LinearIndependent ℂ f := (_root_.Yoland.clear S z q b hg core).comp mission mission.injective
 exact ginJ (R:=(H)) S (pr) y V (fun i:Lead.Clan=> shapeΨ x d j y i t) b hg H' (fun i=> shapeAt x d j y i t ((add_le_add_left (show (score i:ℝ) ≤ core from (by exact_mod_cast (scoring i).2)) _).trans_lt h)) (P.cart_norm 3 ξ (t-c0)) (fun y=> (cartPaste P x y (t-c0))) (fun t y=>(keep_heat (Ω) (P.stone_norm 3 ξ) S (P.heaven_hot 3 ξ) t y).symm)
where ginJ{R:Hilbert}(S:OS.Semigroup R (3:Axis))(L:R.Op)(y:R)(T:R.Op)(g:Lead.Clan→R)(s:ℝ)(hs:0 < s)(H':LinearIndependent ℂ (fun i:Lead.Clan=> detail S (L y) (score i) s))(h:∀i,g i=T (_root_.Yoland.pay S (score i) s y))(p:∀v:R,‖T v‖=‖v‖)(e:∀v:R,T (L v)=L (T v))(r:∀t (z:R),L (S.E t z)=S.E t (L z)):LinearIndependent ℂ (fun i=>L (g i)):=by
        have he : Injective T:=fun i j ht=>by apply sub_eq_zero.mp; apply norm_eq_zero.mp; rw [← p,map_sub,ht,sub_self,norm_zero]
        have hh:LinearIndependent ℂ (fun i:Lead.Clan=> T (detail S (L y) (score i) s)):= H'.map' T.toLinearMap (LinearMap.ker_eq_bot.mpr he)
        simp_rw [_root_.Yoland.paid S (L y) hs, ←_root_.Yoland.turnΩ S y L r _ hs, e,← h] at hh; exact hh
#check LinearIndependent.map'
#print axioms shapeAt
end AuroraB
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

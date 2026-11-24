import Minnow.Cart
import Minnow.Lager
import MarchC.Shirts
import MarchC.Veneer
import MarchC.Item
import Acacia.Tan
import Crape.Creature
import Preen.Fitted
import SatinLocalChron
import Preen.Travel
import GlazeS.Incline
import GlazeS.Room
import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
set_option maxRecDepth 6000
set_option maxHeartbeats 700000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
namespace Mido
open Ballad Cordial
open Lamour.Bridge.Celeste Designs Twah Ballad Cordial Six Habitat.Hemlock.AuroraB
open _root_.YM.Preen Cheer
variable (P:Spine)(x:P.Spectrum0 3)(J:P.Ellis 3 x)(F:ℕ)(C D:ℕ→ℕ→ℝ)(H:Rovers P F C D x)(v:P.Fever F C D x)
local notation "ξ"=>P.otherSpectrum 3 3 x
local notation "W"=>P.ManyF 3 ξ
local notation "Ω"=>P.heaven 3 ξ
local notation "A₀"=>paster (Ω)
local notation "m"=>poseMirror 3
local notation "τ"=>tidal P F
noncomputable def daly (t:Vantage): Matrix Lead.Clan Lead.Clan ℂ:= .of fun i j=> fingering P x F C D i j t
local notation "K"=>daly P x F C D
private def toney(c:Matrix Lead.Clan Lead.Clan ℂ):ℂ:= c.det * ∏ i:Lead.Clan,c i i
private lemma ton_ok(c: Matrix Lead.Clan Lead.Clan ℂ): toney c≠0 ↔ ReadsSix c:=by rw [toney,mul_ne_zero_iff,Finset.prod_ne_zero_iff]; simp [ReadsSix]
include J H
lemma dialsA : slices (toney ∘ K):=by
 intro a y t p; let G(t):= K (update y a t)
 unfold toney
 have he(i j:Lead.Clan):AnalyticAt ℝ (fun t=> G t i j) t:=aligned P x J F C D H a y t (score i+score j) p
 refine AnalyticAt.mul ?_ (Finset.analyticAt_fun_prod _ (fun i _=>he i i))
 change AnalyticAt ℝ (fun t=> (G t).det) t
 simp_rw [Matrix.det_apply']
 exact Finset.analyticAt_fun_sum _ fun b _=> analyticAt_const.mul (Finset.analyticAt_fun_prod _ (fun i _=> he _ _))
noncomputable def stageKM (j:ℕ)(v:W)(a b:Vantage): Matrix Lead.Clan Lead.Clan ℂ:=proto (W) (Ω) (fun i=> shapeΨ x F j v i (m a),fun i=> shapeΨ x F j v i b)
variable (a b:Vantage)(j:ℕ)(t:P.ManyF 3 (P.otherSpectrum 3 3 x))(f:Aloft.PeriodS P F C D x j t)
include f
lemma palmK(hj:F ≤ j)(h:b-a∈mzone)(ha:(core:ℝ)+τ j < -a 3)(hb:(core:ℝ)+τ j < b 3): stageKM P x F j t a b= K (b-a):=by
 have hc:0≤(core:ℝ):=Nat.cast_nonneg _
 ext1 i k; let t':=paster (P.heaven 3 ξ)
 have he(i:Lead.Clan)(a:Vantage)(h:(core:ℝ)+τ j < a 3): shapeΨ x F j t i a=noferal P x F j t a i:=shapeAt x F j t i a (by linarith only [show (score i:ℝ) ≤ core from (by exact_mod_cast (scoring i).2), h])
 exact (congrArg₂ (fun (u v:(W))=> inner ℂ (t' u) (t' v)) (he i (m a) (by rw [clock_neg]; exact ha)) (he k b hb)).trans (funding P x J F C D H j t f a b (lt_of_le_of_lt (le_add_of_nonneg_left hc) ha) ((le_add_of_nonneg_left hc).trans_lt hb) h hj i k)
omit f J H
lemma petite : Continuous (fun q:Vantage×Vantage=> stageKM P x F j t q.1 q.2):= (firing (W) (Ω)).comp ((continuous_pi (fun i=>(shapeC x F j t i).comp ((m).continuous.comp continuous_fst))).prodMk (continuous_pi (fun i=>(shapeC x F j t i).comp continuous_snd)))
include f
lemma petal (h:¬FiniteDimensional ℂ (Aloft.asset P x (A₀ t)))(c:ℝ)(hc:(core:ℝ)+τ j <c): ReadsSix (stageKM P x F j t ((m).symm (forest c)) (forest c)):=by
 let z:=forest c
 let D(i:Lead.Clan):=A₀ (shapeΨ x F j t i z)
 have hv:(core:ℝ)+τ j < z 3:=by unfold z forest; rw [if_pos rfl]; exact hc
 have ht:= shapeLive x F j t h z hv
 have e:ReadsSix (Matrix.gram ℂ D):=grand (R:=(W)) D ht
 have hp:stageKM P x F j t ((m).symm z) z= Matrix.gram ℂ D:=by
    ext1 i l; let V(s):= A₀ (shapeΨ x F j t i s)
    exact congrArg (fun s=> inner ℂ (V s) (D _)) ((m).apply_symm_apply z)
 exact hp.symm ▸ e
where grand {R:Hilbert}(D:Lead.Clan→R.space)(h:LinearIndependent ℂ D):ReadsSix (Matrix.gram ℂ D):= ⟨Matrix.det_gram_ne_zero_iff_linearIndependent.mpr h, fun i e=> h.ne_zero i (inner_self_eq_zero.mp e)⟩
omit f
include J H v
omit J H v in
private lemma stageAt(g:ℝ)(h:0≤g)
 (y:Vantage→Vantage→CrossRead)(he:Continuous (fun z:Vantage×Vantage=>y z.1 z.2))(p: ∀t:ℝ,g<t→ ReadsSix (y ((m).symm (forest t)) (forest t))): ∃i b:Vantage, b-i∈mzone∧g< -i 3∧g<b 3∧ReadsSix (y i b):=by
 let u:=g+1
 have hC:g<u:=lt_add_one _; have hp:0<u:=h.trans_lt hC
 let f:=(m).symm (forest u); let w:=forest u; have hw:w 3=u:=by simp [w,forest]
 have hu:f 3= -u:=by change opposeR 3 (forest u) 3=_; unfold opposeR mirrorΩ; simp [forest]
 let z(c:ℝ):=appoint u c
 have hk: Continuous z:=continuous_pi (fun i=>by
    by_cases h:i=(3:Axis)
    · simpa [z,appoint,h] using (continuous_const : Continuous (fun _ : ℝ=> u))
    simp [z,appoint,h]; exact continuous_id)
 let Pz(c:ℝ):Vantage×Vantage:=(f,z c); have hP:Continuous Pz:=continuous_const.prodMk hk

 have hy: Continuous (fun i=> y f (z i)):= he.comp hP
 have hq: ReadsSix (y f (z 0)):= p u hC -- e not used binder? include f.Proof
 obtain ⟨c,l,h₁⟩:= Filter.Eventually.exists ((show ∀ᶠ c:ℝ in 𝓝[>] (0:ℝ),0<c from self_mem_nhdsWithin).and (((hy.tendsto 0).eventually (readsSix_open.mem_nhds hq)).filter_mono nhdsWithin_le_nhds))
 let Wc:=z c; have hq': Wc 3=u:=by simp [Wc,z,appoint]
 have hx:Wc-f∈mzone:=by
    intro i; rw [Pi.sub_apply]; by_cases g:i=(3:Axis); subst i; rw [hu,hq']; linarith only [hp]
    change 0 < _-opposeR 3 (forest u) i; simp [Wc,z,appoint,g,forest,opposeR,mirrorΩ,l]
 exact ⟨f,Wc,hx,(by rw [hu,neg_neg];exact hC),(by rw [hq'];exact hC),h₁⟩
lemma spansR:∃ p∈mzone,ReadsSix (K p):=by
 obtain ⟨v',e,r⟩:=v F le_rfl
 obtain ⟨a,b,hx,ha,hb,hw⟩:= stageAt ((core:ℝ)+τ F) (add_nonneg (by positivity) (tide_price _ _ _).le) (stageKM P x F F v') (petite P x F F v') (fun t h=>petal P x F C D F v' e r t h)
 exact ⟨_,hx,(congrArg ReadsSix (palmK P x J F C D H a b F v' e (le_refl _) hx ha hb)).mp hw⟩
lemma zone_points{Y Z:Doorway}(p:Y.Later Z orderV 0):∃ a b:Vantage,a∈Y.invites∧b∈Z.invites∧ReadsSix (K (b-a)):=by
 let F':= toney ∘ K
 obtain ⟨p',ht,w⟩:= spansR P x J F C D H v
 obtain ⟨a,b,h,g,t⟩:= thicket p F' (dialsA P x J F C D H) ⟨p',ht,(ton_ok _).2 w⟩
 exact ⟨a,b,h,g,(ton_ok _).1 t⟩
#print axioms zone_points
end Mido
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

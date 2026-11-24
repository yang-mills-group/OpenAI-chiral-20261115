import SatinPP.Octave
import SatinThinJetsPurchase
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3500
set_option maxHeartbeats 650000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six MacroGrid

open TopologicalSpace SatinJets
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "G"=> P.ManyF 3 ξ
local notation "Γ"=> P.cartage 3 ξ
local notation "Θ"=> P.seasons 3 ξ
local notation "E"=> (Θ).E
local notation "κ"=> P.wealth 3 ξ
local notation "D" s:max=>P.lengthP s
local notation "F%" s:max=> P.pointEra s
variable (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))

local notation "ℒ"=>Lead.Clan

/-- rescaled Gram kernels. -/
def Wtime (t h:ℝ):ℂ:= (gloss (aglow 3 t)-gloss (aglow 3 (t+h))-gloss (aglow 3 (t+h))+gloss (aglow 3 (t+h+h))) / (h:ℂ)^2
def Wspace (j:Axis)(t h:ℝ):ℂ:= (gloss (aglow 3 t)-gloss (starLane 3 (aglow j h) t)-gloss (starLane 3 (-aglow j h) t)+gloss (aglow 3 t))/(h:ℂ)^2
def leg (j:Axis):ℝ:= if j=2 then 6 else 0
lemma legs (j:Axis)(w:j≠3)(s:ℝ){t:ℝ}(p:0<t) : gloss (starLane 3 (aglow j s) t)=(↑((s^4+t^4-leg j*s^2*t^2)/(s^2+t^2)^6):ℂ):= by
 have he:starLane 3 (aglow j s) t ≠0:= by 
   intro h; have :t=0:=by simpa [starLane] using congrFun h (3:Axis)
   exact p.ne' this
 rw [heyday _ he]; congr 1
 fin_cases j <;> first
   | exact absurd rfl w
   | simp (config:={decide:=true}) [starLane,aglow,Function.update, leg,pth,tilt]

def numer (a t h:ℝ) :ℝ:=
  2*((6+a)*t^10+14*t^8*h^2+20*t^6*h^4+15*t^4*h^6+6*t^2*h^8+h^10)
lemma space_step (j:Axis)(w:j≠3){t:ℝ}(p:0<t):
 Tendsto (Wspace j t) (𝓝[>] (0:ℝ)) (𝓝 (↑((2*(6+leg j))/t^10:ℝ):ℂ)):= by
 let f h:= numer (leg j) t h /(t^8*(h^2+t^2)^6)
 have he: Continuous f := by
    unfold f numer
    apply Continuous.div <;> first | fun_prop | intro; positivity
 have d:= (Complex.continuous_ofReal.comp he).continuousWithinAt (s:=Set.Ioi (0:ℝ)) (x:=0)
 have hc:f 0=2*(6+leg j)/t^10:= by
    unfold f numer;simp
    field_simp
 rw [←hc]; refine d.tendsto.congr' ?_
 filter_upwards [self_mem_nhdsWithin] with h y; have z:0<h:=y
 have hx:-aglow j h= aglow j (-h):= by ext k;simp [aglow, Function.update];split_ifs <;>simp
 change (f h:ℂ)=Wspace j t h
 unfold Wspace; rw [hx,solo_aglow t p,legs j w h p,legs j w (-h) p]
 norm_cast
 unfold f numer
 field_simp
 ring


def Tnumer (t h:ℝ) :ℝ:=72*h^0*t^14+1008*h^1*t^13+6636*h^2*t^12+27216*h^3*t^11+77784*h^4*t^10+164304*h^5*t^9+265218*h^6*t^8+332688*h^7*t^7+325360*h^8*t^6+245952*h^9*t^5+140896*h^10*t^4+59136*h^11*t^3+17152*h^12*t^2+3072*h^13*t^1+256*h^14*t^0
set_option maxHeartbeats 2000000 in
lemma time_step {t:ℝ}(p:0<t):
 Tendsto (Wtime t) (𝓝[>] (0:ℝ)) (𝓝 (↑(72/t^10:ℝ):ℂ)):= by
 let f h:= Tnumer t h / (t^8*(t+h)^8*(t+h+h)^8)
 have he:ContinuousAt f 0:= by
    unfold f Tnumer
    apply ContinuousAt.div <;> first | fun_prop | dsimp;positivity
 have d:= (Complex.continuous_ofReal.continuousAt.comp he).continuousWithinAt (s:=Set.Ioi (0:ℝ))
 have hc:f 0=72/t^10:= by
    unfold f Tnumer;simp
    field_simp
 rw [←hc]; refine d.tendsto.congr' ?_
 filter_upwards [self_mem_nhdsWithin] with h y; have z:0<h:=y
 change (f h:ℂ)=Wtime t h
 unfold Wtime; rw [solo_aglow t p,solo_aglow _ (by positivity),solo_aglow _ (by positivity)]
 norm_cast
 unfold f Tnumer
 field_simp
 ring


def millrace(i:Fin 6):ℝ:= 2*64^(i.val)
def cavalier(a:ℒ):ℝ:= millrace (family_six a)
lemma cavalry(a:ℒ): 1<cavalier a:= by
 rw [cavalier,millrace]; linarith only [one_le_pow₀ (show (1:ℝ)≤64 by norm_num) (n:=(family_six a).val)]
abbrev squire(a:ℒ):ℝ:= (2*cavalier a)^5
private lemma steep (a b:ℒ):|squire a*squire b/(cavalier a+cavalier b)^10-(if a=b then 1 else 0)|<1/10000:=by
 rw [show (if a=b then (1:ℝ) else 0) = if family_six a=family_six b then 1 else 0 by simp]
 unfold squire cavalier; generalize family_six a=i; generalize family_six b=j
 fin_cases i <;> fin_cases j <;> norm_num [millrace] -- 


def shadowPay (k:ℝ)(a b:ℒ):ℂ:= if a=b then k else 0
lemma steep_net {K:ℝ}(e:|K|≤72){f: ℝ→ℝ→ℂ}
   (h:∀t>1, Tendsto (f t) (𝓝[>] 0) (𝓝 (↑(K/t^10:ℝ):ℂ))):
 ∀ᶠ z in 𝓝[>] (0:ℝ), ∀a b:ℒ, dist ((squire a:ℂ)*squire b*f (cavalier a+cavalier b) z) (shadowPay K a b)<1/100:=by
 refine eventually_all.mpr fun a=>eventually_all.mpr fun b=>?_
 let d:=cavalier a+cavalier b
 let X:ℂ:=(squire a:ℂ)*squire b
 refine (((h d (by unfold d;linarith only [cavalry a,cavalry b])).const_mul X).dist tendsto_const_nhds).eventually (gt_mem_nhds ?_)
 have hx:X*(↑(K/d^10:ℝ):ℂ)-shadowPay K a b=(↑(K*(squire a*squire b/d^10-(if a=b then 1 else 0)):ℝ):ℂ):= by
    unfold X shadowPay;split_ifs <;> push_cast <;> ring
 rw [dist_eq_norm,hx,Complex.norm_real,Real.norm_eq_abs,abs_mul]
 refine (mul_le_mul e (steep a b).le (abs_nonneg _) (by norm_num)).trans_lt ?_
 norm_num
def tBuy(h:ℝ):Prop:=∀ a b:ℒ, dist ((squire a:ℂ)*squire b*Wtime (cavalier a+cavalier b) h) (shadowPay 72 a b)<1/100

def sLeg(j:Axis):ℝ:=2*(6+leg j)
lemma sleg_cost(j:Axis):|sLeg j|≤24:=by unfold sLeg leg;split_ifs<;>norm_num
def zBuy(z:ℝ):Prop:=∀ j:Axis, j≠3→ ∀ a b:ℒ, dist ((squire a:ℂ)*squire b*Wspace j (cavalier a+cavalier b) z) (shadowPay (sLeg j) a b)<1/100
lemma tsBought:∀ᶠ z in 𝓝[>] (0:ℝ), tBuy z ∧ zBuy z:= by
 refine (steep_net (K:=72) (by norm_num) (fun t u=>time_step (zero_lt_one.trans u))).and ?_
 unfold zBuy
 exact eventually_all.mpr fun j=> eventually_all.mpr fun e=> steep_net ((sleg_cost j).trans (by norm_num)) (fun t u=>space_step j e (zero_lt_one.trans u))


import Merino.Medal.Table
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Medal
open Filter Topology Lattice Lat Tulip Branch Cube Tenant Vale RG
open scoped Matrix Matrix.Norms.L2Operator Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Py.Rate Py.Rate.LocalLimit Preparation
open Skye Scree Buffered Afterglow MeasureTheory
open Yoke Papal Garter Gleam
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))

variable {s i k:ℕ}{A:ℝ}
open Pressure.Worth Py.Rate.Pannier
open clocks
local notation "G"=> RootBook Y i k s
local notation "λt"=>hat P.R.L P.x s
local notation "M"=>count Y s i
local notation "g"=>meterC (hat P.R.L P.x s)
local notation "D"=>sites (count Y s i)
local notation "zR"=> gateC (hat P.R.L P.x s)

local notation "a"=>rankFee Y s i k
local notation "T"=>winterBill Y s i k
local notation "R"=>gBaseR Y s i k
local notation "V"=> (Y.voyage i).CapeT s
local notation "E"=> Real.exp
variable {φ:Pane (count Y s i)→ℝ}{L:ℝ}{f:Pane (count Y s i)→ℂ}


/-- per-site overprice (non-tilt) -/
def dusk (x:ℝ):=12*meterC x+oar x
lemma penned0 (u:ShelterCost A Y s i k)(d:coolR Y s i k (2*zR))(p:∀x,‖f x‖ ≤ E (φ x))
  (e:Envelope φ) (b:(∫ x,T x*E (2*φ x)∂Wilson.prior SU.group (More M)) ≤ E (winterRent Y s i k+2*L)) :
  ‖markedRead (icon f) V (denZ G P.U V)‖ ≤
   E (R+(7*g+oar λt)*D+L+(a+4*g*D)):=by
 obtain ⟨x,y⟩:=shade_prior Y u.load u.load.ready d
 obtain ⟨q,h⟩:=tablet Y e b
 let α:=E (a+4*g*D)
 let J:= R+(7*g+oar λt)*D+L
 have h':E L * E (R+7*g*D)≤ E J:=by
   rw [←Real.exp_add];apply Real.exp_monotone
   have M₀:=u.load.clear;have h₀:0≤oar λt*D:=by unfold oar; exact mul_nonneg (by positivity) (zero_le_one.trans (sites_pos _))
   unfold J;linarith only [h₀]


 have h'':E (-L)* E (R+oar λt*D+2*L)≤ E J:= by
    rw [←Real.exp_add];apply Real.exp_monotone
    have g₀:0≤ g:=u.load.health.2.2.1.le.trans u.load.health.2.2.2.1
    unfold J;linarith only [mul_nonneg g₀ (zero_le_one.trans (sites_pos M))]
 apply le_trans (norm_integral_le_of_norm_le
  ((((x.const_mul (E L)).fun_add (q.const_mul (E (-L)))).div_const 2).const_mul α)
  (ae_of_all _ <|retouch Y u p (L:=L)))
 simp only [integral_const_mul, integral_div,
    integral_add (x.const_mul _) (q.const_mul _)]
 -- inference
 rw [add_comm _ (a+4*g*_),
   Real.exp_add (a+4*g*_)]
 refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
 have hy:=
   (mul_le_mul_of_nonneg_left y (Real.exp_pos L).le).trans h'
 have hx:=
   (mul_le_mul_of_nonneg_left h (Real.exp_pos (-L)).le).trans h''
 exact (div_le_div_of_nonneg_right (add_le_add hy hx) (by norm_num:(0:ℝ)≤2)).trans_eq
    (show _=E J by ring)


lemma penned (u:ShelterCost A Y s i k)(d:coolR Y s i k (2*zR))(p:∀x,‖f x‖ ≤ E (φ x))
  (e:Envelope φ) (b:(∫ x,T x*E (2*φ x)∂Wilson.prior SU.group (More M)) ≤ E (winterRent Y s i k+2*L)) :
  ‖Journey.compass Y i k s (icon f)‖ ≤ E (L+dusk λt*D) :=by
 have h:=illumination Y u.load
 rw [Journey.compass,norm_div,div_le_iff₀ ((Real.exp_pos _).trans_le h)]
 apply (penned0 Y u d p e b).trans
 refine le_trans ?_ (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le)
 rw [←Real.exp_add,dusk]; exact le_of_eq (congrArg _ (by ring))

universe h
open Hem
def stint (s i k:ℕ)(F:Pane (count Y s i)→ℂ)(U:Bundle SU.group (More (count Y s i)))
 :Prop:=
 let t:=hat P.R.L P.x s
 let b:= (Papal.gram Y s i k).beta
 ∀ {I:Type h}[Fintype I](c:Garter.Duo (More (count Y s i)))(j:I→StepIn (More (count Y s i)))(w:I→Tint),
   Pavilion (wiggle (clocks.height t)) c j → ∀ z,|z|≤ tiltB t→
   ‖Journey.compass Y i k s (icon (fun x=>∏ d,flipper b z ((j d).rotate c) (w d) F x))‖≤
     Real.exp (advent (Fintype.card I) t (chat Y s i k U c) z+dusk t*sites (count Y s i))


lemma codified (u:ShelterCost A Y s i k)(d:coolR Y s i k (2*zR))
   {F U}(r:Writ.{h} Y s i k F U):stint.{h} Y s i k F U:=by
 dsimp only [stint]
 intro I _ c j w p z q
 obtain ⟨e,y,b⟩:=r c j w p z q
 exact penned Y u d y e b

lemma polarReady :
 ∀ᶠ s in atTop,∀ i k:ℕ,s ≤ Y.uv k→coolR Y s i k (2*gateC (hat P.R.L P.x s)):=by
 filter_upwards [(stage_slope P.V P.x).eventually
    (Tempest.rain_upper P.K.top.clip 2)] with s w i k p
 exact w _ (prices_plot Y s i k p).2.2.2.1.1
#check Tempest.rain_upper

end YM.CF.Merino.Medal

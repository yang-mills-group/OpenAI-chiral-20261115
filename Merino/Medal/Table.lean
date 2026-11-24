import Merino.Medal.Weight
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
local notation "V"=> (Y.voyage i).CapeT s
local notation "R"=>gBaseR Y s i k
local notation "T"=>winterBill Y s i k
open clocks
open Real (exp)

/-- tilted log scene likelihood -/
abbrev Table(y:Course P (VolumeCape.Dream.Nimbus ℓ))(s i k:ℕ)(φ:Pane (count y s i)→ℝ)
   (x:Orbit (count y s i)) := winterBill y s i k x.1*exp (2*φ x.1)



lemma blend (X e u q b L:ℝ)(r:0≤e) : Real.exp b * Real.exp (u+q+X)≤
  Real.exp u*
   ((Real.exp L*Real.exp (X+2*q)+Real.exp (-L)* (Real.exp (X+e)*Real.exp (2*b)))/2):=by
 rw [←Real.exp_add,show b+(u+q+X) = u+(X+b+q) from by ring,Real.exp_add]
 refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
 apply le_trans (b:=(Real.exp ((L+X)+2*q)+Real.exp ((-L+X)+2*b))/2)
 · have h:=Real.add_one_le_exp (L+q-b)
   have k:=Real.add_one_le_exp (-(L+q-b))
   have t:2≤Real.exp (L+q-b)+Real.exp (-(L+q-b)):=by linarith only [h,k]
   have a₁:= mul_le_mul_of_nonneg_left t (Real.exp_pos (X+b+q)).le
   rw [mul_add,←Real.exp_add,←Real.exp_add,
     show X+b+q+(L+q-b)=(L+X)+2*q by ring,
     show X+b+q+-(L+q-b)=(-L+X)+2*b by ring] at a₁
   linarith only [a₁]
 rw [←Real.exp_add,←Real.exp_add (X+e),←Real.exp_add]
 exact div_le_div_of_nonneg_right (add_le_add (by rw [add_assoc])
    (Real.exp_monotone (by linarith only [r]))) (by positivity)
#check polar_env
#check Envelope.mul
#check Yoke.shadeY
#print beam_nil


abbrev icon {n:Side}(f:Pane n→ℂ): Mark n:=fun x=> f x.1•1
local notation "E" => Real.exp
variable {φ:Pane (count Y s i)→ℝ}{L:ℝ}{f:Pane (count Y s i)→ℂ}

lemma retouch (u:ShelterCost A Y s i k)(p:∀x,‖f x‖ ≤ E (φ x)) (x:Orbit M):
   ‖letterRead (f x.1•1) (denZ G P.U V x)‖ ≤ E (a+4*g*D)*
       ((E L*shadeY Y s i k 0 (2*zR) x + E (-L)*Table Y s i k φ x)/2):=by
 rw [(mark_linear 1 1 _ _).2,norm_mul, ← beam_nil]
 have h:=wig Y u x
 apply (mul_le_mul (p _) h (norm_nonneg _) (Real.exp_pos _).le).trans
 rw [sub_eq_add_neg]
 let X:=- (G).path.inChannels (G).funds (G).p (G).beta x.1
 let q:=zR*flakes (shieldC λt) x.1
 obtain ⟨_,b,d,_⟩:= prices_plot Y s i k u.load.paid
 have Z: Papal.frost_bill Y s i k λt 0 (2*zR) x.1 = E (X+2*q):=by
    change E ((X+0 * _)+ _)=_
    unfold q;rw [zero_mul,add_zero,mul_assoc]


 rw [shadeY,Z,Table,winterBill,polarBill,←b,←d]
 have t₀:0 ≤ stipd (grain λt) (ledge λt) (meek (Papal.gram Y s i k).p x.1) (outerMark λt) x.1:=by
     have a₀:=u.load.clear
     unfold stipd grain ledge; positivity
 exact blend X _ _ q _ L t₀

lemma tablet (p:Envelope φ) 
  (b:(∫ x,T x * E (2*φ x) ∂ Wilson.prior SU.group (More M)) ≤ E (winterRent Y s i k+2*L)):
  Integrable (Table Y s i k φ) (city M)∧
   (∫ x,Table Y s i k φ x ∂city M) ≤ E (R+oar λt*D+2*L) :=by
 let F:=fun x=> T x * E (2*φ x)
 let μ:=Wilson.prior SU.group (More M)
 have t:Integrable F μ:= ((polar_env (P.V.L.mood (Y.uv k-s))).mul ((Envelope.const _).mul p).exp).integrable _
 exact ⟨(measurePreserving_fst (μ:=μ) (ν:=depot _)).integrable_comp_of_integrable t,
           (CF.Window.usesPrior F t).trans_le b⟩

end YM.CF.Merino.Medal


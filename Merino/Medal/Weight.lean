import SatinThinBases
import Merino.Garter.Pearl
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



abbrev rankFee (Y:Course P (VolumeCape.Dream.Nimbus ℓ))(s i k:ℕ):ℝ:=
    Cascade.angleFin (RootBook Y i k s).J.M (count Y s i) P.K.j+
      (RootBook Y i k s).v.re
local notation "a"=>rankFee Y s i k
local notation "V"=> (Y.voyage i).CapeT s
lemma wig (u:ShelterCost A Y s i k)(x:Orbit M):
 ‖beamZ M (denZ G P.U V x)‖ ≤ Real.exp
   (a+4*g*D + zR*Py.Rate.Pannier.flakes (shieldC λt) x.1
     - (G).path.inChannels (G).funds (G).p (G).beta x.1):= by
   have h:‖beamZ M (denZ G P.U V x)‖=
     Real.exp (G).v.re *‖beamZ M (Graph.recX P.U G V x)‖:= by
       rw [beamZ,beamZ,Graph.recX,inner_smul_right,norm_mul,
          Complex.norm_exp,Complex.neg_re,←mul_assoc,←Real.exp_add]
       simp
   rw [h]
   apply le_trans (mul_le_mul_of_nonneg_left
      (seeBase Y s i k A u.load.paid u.pose x (atFrame Y s i x)) (Real.exp_pos _).le)
   rw [Graph.past,←Real.exp_add,←Real.exp_add];apply Real.exp_monotone
   have hu :=
     mul_le_mul_of_nonneg_right u.load.health.2.1 (zero_le_one.trans (sites_pos M))
   unfold rankFee
   linarith only [u.effort x,hu]
#print Py.Rate.Pannier.flakes
#check mark_linear


lemma illumination (u:ShelterRent Y s i k):
 Real.exp (a + gBaseR Y s i k - g*D) ≤ ‖coined Y i k s‖:=by
 let h:=u.vast
 simp only [VLine,compensated,norm_mul,Complex.norm_exp,Complex.neg_re] at h
 rw [show a+ gBaseR Y s i k-g*D=(G).v.re+(sod Y k s i - g*D) from ?_,Real.exp_add]
 swap; · change (_ + ((G).v.re)) + (gBaseR Y s i k)- _=_ + ((gBaseR Y s i k+Cascade.angleFin (G).J.M M P.K.j)-_);ring
 exact (mul_le_mul_of_nonneg_left
    ((Real.exp_monotone (sub_le_sub_left (mul_le_mul_of_nonneg_right
       u.health.1 (zero_le_one.trans (sites_pos M))) _)).trans h)
     (Real.exp_pos _).le).trans_eq (by rw [←mul_assoc,←Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul])
#print sod
#print clocks.ledge
#print clocks.grain


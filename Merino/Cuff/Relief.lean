import Merino.Cuff.Tab
import Merino.Cuff.Wale
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Cuff
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n:Side}
local notation "I"=> Single n

open Push.Uniform Planned.JetPort Peaks
open scoped ContDiff
variable {N:Side}
abbrev Tit (N:Side):= BoltIx group N
variable {a C:ℝ}{k:ℕ}{o:Site N}{H:Wheel N}


open Extra.Iteration (momentPrice spendMoment momentPrice_pos)

def tow (a:ℝ):=
 (400*momentPrice 2 (a/4))*(Fintype.card (Chips group)*(Fintype.card Axis*Push.Uniform.countCost (a/4)))

def lengthPay (a:ℝ)(o:Site N)(i:Tit N):= selvage a o i.1 * odds o i
lemma lengthPay_nn (a:ℝ)(o:Site N)(i:Tit N):0≤lengthPay a o i:=
 mul_nonneg (selv_pos ..).le (odds_pos ..)

lemma towed (v:0<a)(o:Site N): (∑ i:Tit N,lengthPay a o i) ≤ tow a:=by
 have p:0<a/4:=by positivity
 let D:=400*momentPrice 2 (a/4)
 have hd:0≤D:=mul_nonneg (by norm_num) (momentPrice_pos _ p).le
 have h(i:Tit N): lengthPay a o i≤D*Decay (a/4) o i.1.1:=by
   let z:ℝ:=separation o i.1.1
   have hn:0≤z:=by unfold z; positivity
   have hp:odds o i≤D*Real.exp (a/4*z):=by
     unfold odds leadPrice lead; push_cast; change 4*(9*(z+1)+1)^2 ≤ _
     rw [show D*Real.exp (a/4*z)=400*(momentPrice 2 (a/4)* Real.exp (a/4*z)) by unfold D; ring]
     refine le_trans ?_ (mul_le_mul_of_nonneg_left (spendMoment 2 p hn) (by norm_num: (0:ℝ)≤400))
     nlinarith
   refine (mul_le_mul_of_nonneg_left hp (selv_pos ..).le).trans_eq ?_


   unfold Decay selvage
   rw [mul_left_comm,← Real.exp_add]; congr 2; unfold z; ring
 refine (sum_le_sum fun i _=>h i).trans ?_
 unfold tow
 rw [← Finset.mul_sum]
 apply mul_le_mul_of_nonneg_left _ hd
 rw [Fintype.sum_prod_type]
 simp_rw [Finset.sum_const,card_univ,nsmul_eq_mul,←Finset.mul_sum]
 rw [Fintype.sum_prod_type]
 simp_rw [Finset.sum_const,card_univ,nsmul_eq_mul,←Finset.mul_sum]
 gcongr
 exact decay_count p _


abbrev bobbin (i:Tit N):Axle N:= staple i.1 (gem i.2)
abbrev tramel (H:Wheel N):Inky (Tit N):=fun i j=> H (bobbin i) (bobbin j)

lemma fabric (x:Axle N):x=∑ i:Tit N, eseed x i • bobbin i:=by
 funext j
 rw [Fintype.sum_prod_type]
 simp only [Finset.sum_apply,Pi.smul_apply]
 rw [sum_eq_single_of_mem j (mem_univ _)]
 · unfold bobbin eseed staple
   simp only [Pi.single_eq_same]
   exact jewels _
 intro i _ ij
 unfold bobbin staple
 simp [ij.symm]

lemma fabric_wheel (x y:Axle N)(H:Wheel N):
  H x y=dripQ (tramel H) (eseed x) (eseed y):=by
 conv_lhs =>
   rw [fabric x,fabric y]
   simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,smul_eq_mul,Finset.mul_sum]; rw [sum_comm]
 exact sum_congr rfl fun i _=>sum_congr rfl fun j _=>by unfold tramel; ring


theorem Linked.cover (v:0<a)(x:Linked a C o k H)(p:lead k<N.val):
   ∃ T:Inky (Husk group N), Sheath o (lead k) (C*(tow a)^2) T ∧
     ∀ y z:Axle N, H y z=dripQ T (cseed y) (cseed z):=by
 obtain ⟨L,h⟩:=pickGroove group o p
 let U:=tramel H
 have hx:symmetric U:=fun i j=>x.symm _ _
 refine ⟨rebrand L U,⟨rebrand_symm hx _,?_,?_⟩,?_⟩
 · apply le_trans (rebrand_wealth U L _ h.light)
   have u:=towed v o
   have hf:=pow_le_pow_left₀ (sum_nonneg fun _ _=> lengthPay_nn a o _) u 2
   refine le_trans ?_ (mul_le_mul_of_nonneg_left hf x.sell)
   rw [pow_two,Finset.sum_mul,mul_sum]
   apply sum_le_sum; intro i _
   rw [mul_sum,mul_sum]; apply sum_le_sum; intro j _
   have hi:= x.earns i.1 j.1 _ _ (gem_norm i.2).le (gem_norm j.2).le
   exact (mul_le_mul_of_nonneg_right hi (mul_nonneg (odds_pos o i) (odds_pos o j))).trans_eq
     (by unfold lengthPay; ring)
 · intro i j hu
   by_contra g
   exact hu (rebrand_vanish (fun t=> by by_contra ht; exact g (h.nearby t i ht)) j)
 intro y z
 let d(t:Axle N):=Font.pure (sap o t)
 have e:H y z = H (y-d y) (z-d z):=by
   rw [H.map_sub,LinearMap.sub_apply,map_sub,x.symm y (d z)]


   have he(t f): H (d t) f=0:=x.exacts _ _
   simp only [he,sub_zero]
 rw [e,fabric_wheel,rebrand_drip]
 apply sum_congr rfl; intro i _
 apply sum_congr rfl; intro j _
 by_cases r:U i j=0
 · change U i j*_ = _
   simp [r]
 have v1:separation o i.1.1≤ k:=le_of_not_gt (fun g=>r (x.van i.1 g _ _))
 have v2:separation o j.1.1≤ k:=le_of_not_gt (fun g=>r ((hx i j).trans (x.van j.1 g _ _)))
 exact congrArg (_ * ·) (congrArg₂ (· * ·) (h.tick y i v1) (h.tick z j v2))
end YM.CF.Merino.Cuff

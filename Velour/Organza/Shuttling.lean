import Velour.Organza.Raising
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 1100
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)

local notation "R" => S.gauze
local notation "D" => S.muslin

open Boundary Probe
local notation "α" => S.dangle
local notation "U" => S.unit.translation

open LineDeriv

lemma unit_second (t:ℝ) : U (t • basis a)= S.edge t:= by
  have h : SEP a (t • basis a)=0:= Subtype.ext (show _ • _ - _= (0:E4) by simp)
  unfold unit; dsimp only; rw [h,S.uZero]; simp


/-- Time derivative detector. -/
def tick (a: Axis) : Test4 →L[ℂ] Test4 := lineDerivOpCLM ℂ Test4 (basis a)

lemma tick_obeys (f:Test4)(b:E4):HasLineDerivAt ℝ f (tick a f b) b (basis a):=f.differentiableAt.hasFDerivAt.hasLineDerivAt _

local notation "γ" => S.E 1
/- On ops with harmless fixed extra padding γ. -/
lemma line_hold (r:ℝ) :
 HasDerivAt (fun t:ℝ=> U ((t*r) • basis a) * γ * R)
   (((r:ℂ)*I) • (γ * (1-R))) 0:= by
 simp_rw [unit_second]
 exact S.raise_lined _ zero_lt_one _

private noncomputable def incline (T:H.Op):=
  I • (γ * (T*R - R*T) * γ)

private lemma line_start (T:H.Op):
 HasDerivAt (fun t:ℝ=> α (t • basis a) (γ * R * T * R * γ))
    (S.incline T) 0:= by
  have k:= ((S.line_hold 1).mul_const T).mul (S.line_hold (-1))
  simp only [mul_one, mul_neg,ofReal_neg,ofReal_one,one_mul,neg_zero,zero_smul,neg_mul, S.unit.origin] at k
  change HasDerivAt _ (I • (γ * (T * R - R * T)* γ)) _
  refine k.congr_of_eventuallyEq (Eventually.of_forall fun b=> ?_) |>.congr_deriv ?_

  · rw [dangle]; simp only [Pi.mul_apply,neg_smul]
    rw [show (U (-(b • basis a))*γ)*R = (R*γ)*U (-(b • basis a)) by
         rw [mul_assoc,(S.gauze_heated _).eq, ((S.unit_weight _).mul_right (S.unit_heat ..)).eq]] -- may target first occurrence (U b)
    simp only [mul_assoc]
  rw [show ContinuousLinearMap.id ℂ H.space=(1:H.Op) from rfl,one_mul,
     (S.gauze_heated _).eq,
     smul_mul_assoc,smul_mul_assoc,neg_smul,mul_neg,mul_smul_comm,
     ← sub_eq_add_neg,← smul_sub] 
  conv_lhs =>
    arg 2; rhs; lhs; lhs
    rw [← (S.gauze_heated _).eq]
  conv_lhs =>
    arg 2; rhs;rhs; rw [((Commute.one_right _).sub_right (S.gauze_heated 1)).eq]
  congr 1
  simp only [mul_sub, sub_mul, mul_one, one_mul, mul_assoc]
  abel




private lemma line_slope (T:H.Op)(b:E4)(v:H.space):
  HasLineDerivAt ℝ (fun y=> α y (γ * R * T * R * γ) v) (α b (S.incline T) v) b (basis a):= by
  have k:= (((S.line_start T).const_mul (U b)).mul_const (U (-b)))
  let L:= (ContinuousLinearMap.apply ℂ H.space v).restrictScalars ℝ
  refine (L.hasFDerivAt.comp_hasDerivAt _ k).congr_of_eventuallyEq (Eventually.of_forall fun t=> ?_)
  change α (b+t • basis a) _ v=α b (α (t • basis a) (γ*R*T*R*γ)) v
  unfold dangle
  rw [neg_add_rev,←S.unit_step,←S.unit_step]
  rfl


private lemma inclined_rasp (T:H.Op)(f:Test4):
 S.rasp (S.incline T) f = - S.rasp (γ * R * T * R * γ) (tick a f):=by
 ext1 x
 exact integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
  (f:=⇑f) (f':=⇑(tick a f))
  (g:= fun b=>α b (γ*R*T*R*γ) x) (g':= fun b=>α b (S.incline T) x)
  (B:=ContinuousLinearMap.lsmul ℝ ℂ)
  (μ:=volume)
  (S.unsoiled ..) (S.unsoiled ..) (S.unsoiled ..)
  (fun b _=> tick_obeys ..) (fun b _=> S.line_slope ..)

/- More smearing properties. -/
lemma rasp_lever (c:ℂ)(T:H.Op) : S.rasp (c • T)= c • S.rasp T:= by
  ext1 f; ext1 v
  change _=c • (S.rasp T f v)
  rw [rasp_apply,rasp_apply, ←integral_smul]
  refine integral_congr_ae (ae_of_all _ fun b=>?_ )
  dsimp only; rw [dangle,dangle,mul_smul_comm,smul_mul_assoc,_root_.smul_apply,smul_comm]
lemma rasp_cutoff (T W:H.Op) : S.rasp (T-W) = S.rasp T - S.rasp W:= by
  ext1 f; ext1 v
  change _= S.rasp T f v-S.rasp W f v
  rw [rasp_apply,rasp_apply,rasp_apply, ←integral_sub (S.unsoiled ..) (S.unsoiled ..)]
  refine integral_congr_ae (ae_of_all _ fun b=>?_ )
  dsimp only; rw [dangle,dangle,dangle,mul_sub,sub_mul,_root_.sub_apply,smul_sub]


lemma equal_heat {d:ℝ≥0}{Y V:H.Op} (t:S.E d * Y * S.E d=S.E d * V * S.E d) : Y=V:= by
 have h₁: Y * S.E d=V * S.E d:= by
    rw [mul_assoc,mul_assoc] at t
    ext1 x; apply sub_eq_zero.mp
    refine S.heat_faithful d _ ?_
    rw [map_sub,←mul_apply_eq_comp,t, mul_apply_eq_comp,sub_self]
 exact ContinuousLinearMap.ext (congrFun ((S.whole d).equalizer Y.continuous V.continuous (congrArg (fun T:H.Op=>⇑T) h₁)))

local notation "C" => S.rasp
def shuttle (a:Axis) : Test4 →L[ℂ] Test4:= I • tick a
/-- Energy transfer, polynomial form. No formal commutators on the domain required. -/
lemma shuttles (T:H.Op)(f:Test4): C T f * R = R * (C T f + C T (shuttle a f) * R):= by
 let X:= C T f
 have h := S.inclined_rasp T f
 have j: C (S.incline T) f=I • (γ * (X * R - R*X) * γ):= by
  unfold incline
  rw [rasp_lever,_root_.smul_apply,
      S.rasp_more_right _ _ (fun b=>S.unit_heat b 1), S.rasp_more_left _ _ (fun b=>S.unit_heat b 1),
      rasp_cutoff,_root_.sub_apply, S.rasp_more_right _ _ S.unit_weight,
      S.rasp_more_left _ _ S.unit_weight]


 let Z:= R * (C T (tick a f) * R)
 rw [j,S.rasp_more_right _ _ (fun b=> S.unit_heat b 1), S.rasp_more_right _ _ S.unit_weight,
     mul_assoc γ R T, S.rasp_more_left _ _ (fun b=> S.unit_heat b 1),
     S.rasp_more_left _ _ S.unit_weight] at h
 have e:=congrArg (-I • ·) h
 rw [smul_smul,neg_mul,I_mul_I,neg_neg, one_smul,neg_smul,smul_neg, neg_neg] at e
 have k: X * R - R*X = I • Z:= by
     apply S.equal_heat (d:=1)
     rw [e]
     dsimp only [Z]
     rw [mul_smul_comm,smul_mul_assoc]; simp only [mul_assoc]
 unfold shuttle
 rw [mul_add, _root_.smul_apply, map_smul, smul_mul_assoc,mul_smul_comm]
 exact (sub_eq_iff_eq_add.mp k).trans (add_comm ..)

#print axioms shuttles


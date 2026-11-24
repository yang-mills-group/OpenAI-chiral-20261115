import YM.CF.BProof.Dream.Sub
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Fixed numerical angles for B-Gz. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Dream
open Matrix Real Finset
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
local notation "τ" => 2*Real.pi/5
lemma fives : 0< τ ∧ cos τ=(√5-1)/4 ∧ cos (3* (τ))= -(1+√5)/4 ∧ cos (3*(2*(τ)))= (√5-1)/4 := by
 constructor; positivity
 have hp: cos (τ)=(√5-1)/4:=by rw [mul_div_assoc,cos_two_mul,Real.cos_pi_div_five]; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)] -- tune
 refine ⟨hp,?_,?_⟩
 · rw [show 3*(τ)=π/5+π from by ring,Real.cos_add_pi,cos_pi_div_five]; ring
 rw [show 3*(2*(τ))=(τ)+2*Real.pi from by ring, cos_add_two_pi,hp]
lemma upBound (t x:ℝ)(h:0≤t)(u:t≤π)(x':-1≤x)(y:x≤1)(w:x<cos t) : t < arccos x :=by
 rw [←show arccos (cos t)=_ from Real.arccos_cos h u]; exact arccos_lt_arccos x' w (cos_le_one _)
lemma downBound (t x:ℝ)(h:0≤t)(u:t≤π)(x':-1≤x)(y:x≤1)(w:cos t<x) : arccos x<t:=by rw [←show arccos (cos t)=_ from Real.arccos_cos h u]; exact arccos_lt_arccos (Real.neg_one_le_cos _) w y
def phaseH(t:ℝ):= (1+cos (3*t))/2
def argH(t:ℝ) := arccos (phaseH t)
lemma phaseH_under(t:ℝ) : -1≤ phaseH t ∧ phaseH t≤1:=by unfold phaseH; constructor <;> linarith [cos_le_one (3*t), Real.neg_one_le_cos (3*t)]
lemma phaseH_ready (t:ℝ): 1+cos (3*t)=2*cos (argH t):=by rw [argH,Real.cos_arccos (phaseH_under t).1 (phaseH_under t).2]; unfold phaseH; ring
lemma split1 : (τ)<argH (τ) ∧ argH (τ)< π/2:=by
 obtain ⟨p,q,h,H⟩:= fives; have hs := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num); have hx:= Real.sqrt_nonneg 5; constructor
 · apply upBound _ _ p.le (by linarith) (phaseH_under _).1 (phaseH_under _).2; rw [phaseH,h,q]; nlinarith
 apply (Real.arccos_lt_pi_div_two).mpr; rw [phaseH,h]; nlinarith
lemma split2 : π/5<argH (2*(τ)) ∧ argH (2*(τ)) < (τ):=by
 obtain ⟨p,q,h,H⟩:= fives; have hs := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num); have hx:= Real.sqrt_nonneg 5; constructor
 · apply upBound _ _ (by positivity) (by linarith) (phaseH_under _).1 (phaseH_under _).2; rw [phaseH,H,cos_pi_div_five]; nlinarith -- compare x=(1+.309)/2=.65<.81 yes
 apply downBound _ _ p.le (by linarith) (phaseH_under _).1 (phaseH_under _).2; rw [phaseH,H,q]; nlinarith
lemma half1 : Whirl (doubleU (τ) (π/4)) (-(τ)*2):=by
 let a:=argH (τ); obtain ⟨ha,hu⟩:=split1; change _< a at ha; change a < _ at hu; have hp:= fives.1; rw [show -(τ)*2= -(τ)+a+(-(τ)+(-a)) from by ring]; exact half _ _ _ _ (phaseH_ready _) (abs_lt.mpr ⟨by linarith,by linarith⟩) (abs_lt.mpr ⟨by linarith,by linarith⟩) rfl rfl
lemma around (t:ℝ): rose (t+2*π)=rose t:=by rw [rose_add,rose_full,mul_one]
lemma half2 : Whirl (doubleU (2*(τ)) (π/4)) (τ) :=by
 let t:ℝ:=2*(τ); let a:=argH t; obtain ⟨ha,hu⟩:=split2; change _< a at ha; change a < _ at hu; have hp:= pi_pos; have hh:t=4*π/5:=by dsimp only [t]; ring
 let p:= -t+a; let q:= -t+(-a)+2*π; suffices h:Whirl (doubleU t (π/4)) (p+q) from (by
    change Whirl (doubleU t _) _; rw [show (τ)=p+q from (by dsimp only [p,q,t]; ring)]; exact h)
 exact half _ _ _ _ (phaseH_ready _) (abs_lt.mpr (show -π < p ∧ p<π from ⟨by dsimp only [p]; linarith,by dsimp only [p]; linarith⟩)) (abs_lt.mpr (show -π<q∧q<π from ⟨by dsimp only [q]; linarith,by dsimp only [q]; linarith⟩)) rfl (around _)
end YM.CF.BProof.Dream

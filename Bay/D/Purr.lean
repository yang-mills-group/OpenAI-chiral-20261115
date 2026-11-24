import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
noncomputable section
namespace YM.CF.Bay.D


variable {K:ℝ}(x y:ℝ)
def pur(K x:ℝ):ℝ:=x/(1+(x/K)^2)
lemma pur_smooth(K:ℝ):ContDiff ℝ 1 (pur K) :=by
 have hr (x:ℝ):(1+(x/K)^2)≠0:=ne_of_gt (by positivity)
 unfold pur
 exact contDiff_id.div (contDiff_const.add ((contDiff_id.div_const K).pow 2)) hr
lemma pur_clip : |pur K x|≤|x|:=by
 rw [pur,abs_div,abs_of_nonneg (by positivity : 0≤1+(x/K)^2)]
 exact div_le_self (abs_nonneg _) (le_add_of_nonneg_right (sq_nonneg _))
lemma pur_max (h:0<K) : |pur K x|≤K:=by
 rw[pur, abs_div,abs_of_nonneg (by positivity:0≤1+(x/K)^2),
     div_le_iff₀ (by positivity)]
 have hx: |x|/K ≤ 1+(x/K)^2:=by
   rw [←abs_of_pos h,←abs_div,abs_of_pos h]
   have :=sq_nonneg ( |x/K| -1)
   rw[sub_sq,sq_abs] at this
   nlinarith [sq_nonneg (x/K)]
 rw[mul_comm K];exact (div_le_iff₀ h).mp hx

lemma pur_bent : |pur K x - x|≤ |x|^3/K^2:=by
 have g:0<1+(x/K)^2:=by positivity
 rw[pur,div_sub' g.ne',show x-(1+(x/K)^2)*x=-(x*(x/K)^2) from by ring,
    abs_div,abs_neg,abs_mul,abs_of_nonneg (sq_nonneg (x/K)),abs_of_pos g]
 apply le_trans (div_le_self (by positivity) (le_add_of_nonneg_right (sq_nonneg _)))
 exact le_of_eq (by rw [div_pow,show (3:ℕ)=2+1 from rfl,pow_succ |x| 2, sq_abs];ring)
lemma pur_lip (K:ℝ) : |pur K x-pur K y| ≤ |x-y|:=by
 let a:=x/K
 let b:=y/K
 have hz:|1-a*b| ≤ (1+a^2)*(1+b^2):=by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (a*b),sq_nonneg (a+b),sq_nonneg (a-b)]
 have hj:0<(1+a^2)*(1+b^2):=by positivity
 unfold pur; rw [div_sub_div _ _ (by positivity) (by positivity),
    show x*(1+b^2)-(1+a^2)*y=(x-y)*(1-a*b) from by unfold a b;ring,
    abs_div,abs_mul,abs_of_pos hj,div_le_iff₀ hj]
 exact mul_le_mul_of_nonneg_left hz (abs_nonneg _)
end YM.CF.Bay.D

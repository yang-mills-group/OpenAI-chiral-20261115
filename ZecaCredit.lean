import ZecaCharge
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S: OS.Semigroup H a)
local notation "R" => saucer S

variable (F:ℝ≥0→ℝ≥0→H.Op) (n:ℕ)
local notation "D"=> Cache S n
lemma cache_D:DenseRange ⇑(D):=by
 apply Dense.mono _ (S.whole 1) -- K_E
 rintro y ⟨x,rfl⟩
 exact ⟨_,DFunLike.congr_fun (K_E S n 1 zero_lt_one) x⟩
variable {A:H.Op}
lemma op_smooth {X Y:H.Op} (p:D*X*D=D*Y*D):X=Y:=by
 exact ContinuousLinearMap.ext (congrFun ((cache_D S n).equalizer X.continuous Y.continuous
    (funext fun y => cache_I S n (DFunLike.congr_fun p y))))


lemma rec_pay (h:credit S F n A){s t:ℝ≥0}(p:0<s)(q:0<t):
   parabola S n (duration s) * A * parabola S n (duration t) = F s t:=by
 apply op_smooth S n
 rw [←mul_assoc,←mul_assoc, K_E S n s p,mul_assoc,change_m S n _ (dur.mpr q),
               S.roots_heat q,h s t p q]
lemma parabolaE (t:ℝ≥0)(p:0<t):
 parabola S n (duration t)*D=S.E t:=
 (change_m S n _ (dur.mpr p)).trans (S.roots_heat p)

lemma hall_parabola (t:ℝ≥0)(p:0<t)(x:H):
 hall S n ⟨S.E t x,ray S x t p⟩ = parabola S n (duration t) x:=by
 apply cache_I S n
 rw [releases]
 exact DFunLike.congr_fun (K_E S n t p).symm x

lemma para_adj (t:ℝ≥0)(p:0<t):
 (parabola S n (duration t)).adjoint = parabola S n (duration t):=by
 let g:=parabola S n (duration t)
 change star g=g
 have q := congrArg Star.star (show g*D=S.E t from parabolaE S n t p)
 rw [star_mul,(show star D=D from (saucer_sym S).pow n), show star (S.E t)=_ from S.sym t] at q
 ext1 x; apply cache_I S n
 exact DFunLike.congr_fun (q.trans (K_E S n t p).symm) x

lemma rec_pair (h:credit S F n A){s t:ℝ≥0}(p:0<s)(q:0<t) (x y:H):
 let X:Bench S:=⟨S.E s x,ray S x s p⟩
 let Y:Bench S:=⟨S.E t y,ray S y t q⟩
 inner ℂ x (F s t y)=inner ℂ (hall S n X) (A (hall S n Y)):=by
 simp only
 rw [←rec_pay S F n h p q]
 rw [hall_parabola _ _ _ p,hall_parabola _ _ _ q,←ContinuousLinearMap.adjoint_inner_right, para_adj _ _ _ p]
 rfl

lemma credit_uniq {X Y:H.Op} (c:credit S F n X)(d:credit S F n Y):X=Y:=by
 -- heat dense & injective
 have p:= (c 1 1 zero_lt_one zero_lt_one).trans (d _ _ zero_lt_one zero_lt_one).symm
 refine ContinuousLinearMap.ext (congrFun ((S.whole 1).equalizer X.continuous Y.continuous
    (funext fun y => ?_)))
 have h:= DFunLike.congr_fun p y
 apply ext_inner_right ℂ
 intro z; induction z using (S.whole 1).induction_on with
 | hp => exact isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
 | ih z =>
   dsimp only [comp_apply]
   rw [←ContinuousLinearMap.adjoint_inner_left (S.E 1),←ContinuousLinearMap.adjoint_inner_left (S.E 1),
       S.sym]
   exact congrArg (inner ℂ · z) h
lemma credit_inv (c:credit S F n A): credit S (fun s t=> star (F t s)) n (star A):=by
 intro s t i j
 simpa only [star_mul,(show star (R^n)=D from (saucer_sym S).pow n),show star (S.E s)=S.E s from S.sym s,
   show star (S.E t)=S.E t from S.sym t,mul_assoc] using
    congrArg Star.star (c t s j i)
#print axioms rec_pair
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca

import Merino.Cuff.Parol
set_option autoImplicit false
noncomputable section
namespace YM.CF.Merino.Garter
open Cuff Finset Function
open scoped BigOperators ContDiff


def bite (e x:ℝ):=x/(1+(e*x)^2)

lemma chew_small (e x:ℝ) : |bite e x| ≤ |x|:=by
 rw [bite,abs_div,abs_of_pos (a:=1+_) (by positivity)]
 exact div_le_self (abs_nonneg _) (le_add_of_nonneg_right (sq_nonneg _))

lemma chew_loss(e x:ℝ):|bite e x-x|≤ e^2*|x|^3 := by
 rw [show bite e x-x= -(e^2*x^2)*bite e x from ?_]
 · rw [abs_mul,abs_neg,abs_of_nonneg (by positivity:(0≤e^2*x^2))]
   refine (mul_le_mul_of_nonneg_left (chew_small ..) (by positivity)).trans_eq ?_
   rw [show |x|^3=|x|^2*|x| from pow_succ ..,sq_abs]; ring -- easier sq_abs
 unfold bite
 have h:0<1+(e*x)^2:=by positivity
 field_simp; ring

lemma chew_bound {M:ℝ}(p:0<M)(x:ℝ) : |bite M⁻¹ x|≤M:=by
 rw [bite,abs_div,abs_of_pos (a:=1+_) (by positivity),div_le_iff₀ (by positivity)]
 have h:M⁻¹ * |x| ≤ 1+(M⁻¹*x)^2:=by
    rw [mul_pow,← sq_abs x,←mul_pow]
    nlinarith only [sq_nonneg (M⁻¹*|x|-1/2)]
 simpa only [←mul_assoc M M⁻¹,mul_inv_cancel₀ p.ne',one_mul] using mul_le_mul_of_nonneg_left h p.le


lemma chew_smooth(e:ℝ):ContDiff ℝ 1 (bite e):=
 (contDiff_id.div ((contDiff_const).add ((contDiff_const.mul contDiff_id).pow 2)) fun x=> by
    exact ne_of_gt (by change 0<1+(e*x)^2; positivity))

lemma chew_soft(e x y:ℝ):|bite e x-bite e y|≤|x-y|:=by
 let u:=e*x; let v:=e*y
 have h:|1-u*v|≤ (1+u^2)*(1+v^2) := by
   apply abs_le.mpr; constructor <;> nlinarith [sq_nonneg (u-v), sq_nonneg (u+v),sq_nonneg (u*v)]
 have a:0<1+u^2:=by positivity
 have b:0<1+v^2:=by positivity
 have t:bite e x-bite e y=(x-y)*(1-u*v)/((1+u^2)*(1+v^2)):=by
    change x/(1+u^2)-y/(1+v^2)=_
    field_simp
    dsimp [u,v]; ring
 rw [t,abs_div,abs_mul,abs_of_pos (mul_pos a b),div_le_iff₀ (mul_pos a b)]
 exact mul_le_mul_of_nonneg_left h (abs_nonneg _)


lemma bleary {x y z w r:ℝ}(h:|x|≤r)(p:|w|≤r):
 |x*y-z*w|≤r*(|y-w|+|x-z|):=by
 rw [show x*y-z*w=x*(y-w)+(x-z)*w from by ring,mul_add]
 apply (abs_add_le ..).trans; rw [abs_mul, abs_mul, mul_comm r |x-z|]
 gcongr
lemma blemish {I:Type*}[Fintype I](a b x y:I→ℝ){r t:ℝ}(s:0≤r)
 (h:∀ i,|a i|≤r)(p:∀ i,|y i|≤r)
 (q:∑ i,|a i-x i|≤t)(e:∑ i,|b i-y i|≤t):
  ∑ i,|a i*b i-x i*y i| ≤ 2*r*t:=by
 apply (sum_le_sum (fun i _=>bleary (y:=b i) (z:=x i) (h i) (p i))).trans
 rw [←mul_sum,sum_add_distrib]
 exact (mul_le_mul_of_nonneg_left (add_le_add e q) s).trans_eq (by ring)


variable {J:Type}[Fintype J]{T:Inky J}{L:ℝ}
def pour (T:Inky J)(f:J→J→ℝ) := ∑ i,∑ j,T i j*f i j
lemma pour_abs (f:J→J→ℝ) {K:ℝ}(h:0≤K)(q:laden T≤L)
 (e:∀ i j,T i j≠0 → |f i j|≤K):
 |pour T f|≤L*K:=by
 refine (abs_sum_le_sum_abs ..).trans (le_trans ?_ (mul_le_mul_of_nonneg_right q h))
 rw [laden_l]; simp_rw [sum_mul]; refine sum_le_sum (fun i _=>(abs_sum_le_sum_abs ..).trans <| sum_le_sum fun j _=>?_)
 rw [abs_mul]; by_cases t:T i j=0
 · rw [t,abs_zero,zero_mul,zero_mul]
 exact mul_le_mul_of_nonneg_left (e i j t) (abs_nonneg _)
lemma pour_sub (f g:J→J→ℝ):pour T f-pour T g=pour T fun i j=>f i j-g i j:=by simp [pour,mul_sub,sum_sub_distrib]

lemma splash {K:ℝ}(f:J→ℝ)(q:laden T≤L)
 (e:∀ i j,T i j≠0 → |f i|≤K ∧ |f j|≤K):
 |dripQ T f f|≤L*K^2:=by
 apply pour_abs _ (sq_nonneg _) q; intro i j h
 rw [abs_mul,pow_two]
 obtain ⟨x,y⟩:=e i j h
 exact mul_le_mul x y (abs_nonneg _) ((abs_nonneg _).trans x)


variable {I:Type*}[Fintype I]
lemma pour_together (p:laden T≤L)(f:I→J→J→ℝ){K:ℝ}(s:0≤K)
 (q:∀ i j,∑ k, |f k i j|≤K):
 ∑ k, |pour T (f k)| ≤ L*K:=by
 refine le_trans (b:=∑ k,∑ i,∑ j,|T i j * f k i j|) ?_ (le_trans ?_ (mul_le_mul_of_nonneg_right p s))
 · exact sum_le_sum fun k _=>(abs_sum_le_sum_abs ..).trans (sum_le_sum fun i _=>abs_sum_le_sum_abs ..)
 rw [sum_comm, laden_l,sum_mul]
 apply sum_le_sum; intro i _
 rw [sum_comm, sum_mul]; apply sum_le_sum; intro j _
 simp_rw [abs_mul]; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (q i j) (abs_nonneg _)
lemma spray (p:laden T≤L)(x y:I→J→ℝ){M K:ℝ}(s:0≤M)(t:0≤K)
 (q:∀ k i, |x k i|≤M)(h:∀ k i,|y k i|≤M)(e:∀i,∑ k, |x k i-y k i|≤K):
 ∑ k, |dripQ T (x k) (x k)-dripQ T (y k) (y k)| ≤ L*(2*M*K):=by
 simp_rw [show ∀ u v, dripQ T u v=pour T (fun i j=>u i*v j) from fun _ _=>rfl,pour_sub]
 exact pour_together p _ (by positivity) fun i j=> blemish _ _ _ _ s (q · i) (h · j) (e _) (e _)

end YM.CF.Merino.Garter

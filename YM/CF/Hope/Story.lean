import YM.CF.Beau.Sign
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Hope
open Function NormedSpace Filter Metric Finset MeasureTheory RG
open scoped Topology ContDiff BigOperators
variable{A:Type*}[NormedCommRing A][NormedAlgebra ℝ A][CompleteSpace A][NormOneClass A]
def bixE (x:A)(i:ℕ):A:= -((1+(i:ℝ))⁻¹ •((-x)^(i+1)))
def pencilT (x:A):=∑' i,bixE x i
lemma text_K (x:A)(p:‖x‖≤1/4): NormedSpace.exp (pencilT x)=1+x:=by
 let F(t:ℝ):A:= t • x
 let V:=ball (0:ℝ) 2; let Z(t):A:=pencilT (F t); let K(t):=∑' i:ℕ,(-F t)^i
 have h(t:ℝ)(v:t∈V): ‖-F t‖≤1/2:=by unfold F; rw [norm_neg,norm_smul]; refine (mul_le_mul (mem_ball_zero_iff.mp v).le p (norm_nonneg _) (by norm_num)).trans (by norm_num)
 have hp(t):HasDerivAt F x t:= (((hasDerivAt_id' t).smul_const x)).congr_deriv (by simp)
 have he(t:ℝ)(i:ℕ):HasDerivAt (fun t=>bixE (F t) i) ((-F t)^i*x) t:=by
    unfold bixE; -- workaround rewrite (-F t)^i = (-t)^i • x^i
    let u:= F t; have hr:= (hp t).neg; -- power via mul deriv? HasDerivAt.pow commℝ generic
    apply HasDerivAt.congr_deriv (((((hr.pow (i+1)).const_smul ((1+i:ℝ)⁻¹))).neg)) -- tune
    simp only [Nat.cast_add,Nat.cast_one]; change -((1+i:ℝ)⁻¹ • ((i+1:A)*(-F t)^((i+1)-1)* (-x)))=_; simp only [mul_neg,smul_neg,neg_neg,Nat.add_sub_cancel]; rw [mul_assoc]; generalize Y:(-F t)^i*x=y; rw [show ((i:A)+1)* y=(1+i:ℝ) • y from ?_, inv_smul_smul₀]; positivity
    rw [Algebra.smul_def, map_add, map_one,map_natCast, add_comm]
 have hg(t)(v:t∈V):HasDerivAt Z (K t*x) t:=by
    unfold Z pencilT K; have hq:Summable (fun i:ℕ=>(-F t)^i):= summable_geometric_of_norm_lt_one (by linarith [h t v]) ; rw [←hq.tsum_mul_right]; let U(i:ℕ):=(1/2:ℝ)^i*‖x‖; have hs:Summable U:= (summable_geometric_of_lt_one (by norm_num) (show (1/2:ℝ)<1 by norm_num)).mul_right _
    apply hasDerivAt_tsum_of_isPreconnected (t:=V) (g':=fun i t=>(-F t)^i*x) hs isOpen_ball ((convex_ball (0:ℝ) 2).isPreconnected) (fun i t _=>he t i) (fun i y hy=>(norm_mul_le ..).trans (mul_le_mul_of_nonneg_right (le_trans (norm_pow_le ..) (pow_le_pow_left₀ (norm_nonneg _) (h y hy) _)) (norm_nonneg _))) (show (0:ℝ)∈V by unfold V; simp) (by simp [bixE,F]) v
 let R(t:ℝ):A:=1+ F t; let Q(t:ℝ):A:=exp (-Z t)*R t
 have hz(t)(v:t∈V): HasDerivAt Q 0 t:=by
    have hx:K t * R t=1:=by rw [show R t=1-(-F t) by unfold R; abel]; exact geom_series_mul_neg _ (by linarith [h t v])
    have hf(t): HasDerivAt R x t:= (hp t).const_add _
    refine ((((hasFDerivAt_exp (x:=-Z t) (𝕂:=ℝ)).comp_hasDerivAt t (hg t v).neg).mul (hf t))).congr_deriv ?_
    change (exp (-Z t)* -(K t*x)) * R t + exp (-Z t)*x=0; rw [show exp _* -(K t*x)*R t=-( (K t*R t)*(exp (-Z t)*x)) from ?_,hx,one_mul]; abel; ring
 have hK:NormedSpace.exp (pencilT x)*exp (-pencilT x)=1:=by
    letI : NormedAlgebra ℚ A:= NormedAlgebra.restrictScalars ℚ ℝ _; rw [← NormedSpace.exp_add, add_neg_cancel,NormedSpace.exp_zero]
 have ht:Q 0=Q 1:=(show IsOpen V from isOpen_ball).is_const_of_deriv_eq_zero ((convex_ball (0:ℝ) 2).isPreconnected) (fun i h=>(hz i h).differentiableAt.differentiableWithinAt) (fun i h=>(hz i h).deriv) (show (0:ℝ)∈V by unfold V; simp) (show (1:ℝ)∈V by unfold V; simp)
 have hq:Q 1=1:=by rw [←ht]; letI : NormedAlgebra ℚ A:= NormedAlgebra.restrictScalars ℚ ℝ _; simp [Q,Z,pencilT,F,bixE,R]
 have hs: exp (-pencilT x)*(1+x)=1:=by unfold Q R Z F at hq; rwa [one_smul] at hq
 calc
    _ = exp (pencilT x) * (exp (-pencilT x)*(1+x)):=by rw [hs,mul_one]
    _ = _:=by rw [←mul_assoc,hK,one_mul]
end YM.CF.Hope

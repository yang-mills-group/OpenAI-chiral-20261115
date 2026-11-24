import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Opera
open Function Set Filter MeasureTheory Metric Real
open scoped BigOperators Topology InnerProductSpace ComplexOrder NNReal ENNReal Complex
local notation "ε"=>Real.exp
local notation "ξ"=>Complex.exp
noncomputable def loft (x:ℝ):= ε (π*x)
def descent (x:ℝ):= loft x/(1+loft x)
local notation "L"=>loft
local notation "P"=>descent
def traces (x:ℝ):= π * P x * (1 - P x)
local notation "τ" => traces
lemma loft_pos (x):0<L x:= Real.exp_pos _
@[fun_prop] lemma continuity : Continuous loft:=by unfold loft; fun_prop
lemma loft_deriv (x): HasDerivAt L (L x*π) x:= by
 let H:= ( ((hasDerivAt_id' x).const_mul π).exp); unfold loft; convert! H using 1<;> ring
lemma reverse (x):1-P x=1/(1+L x):=by
 unfold descent; have h:0<1+L x:=by linarith [loft_pos x]
 field_simp <;> ring
lemma ball (x:ℝ):0<P x∧0<1-P x:= by rw [reverse]; unfold descent; have h:=loft_pos x; constructor<;>positivity
lemma day (x): HasDerivAt P (τ x) x:= by
 have h:0<1+L x:=add_pos zero_lt_one (loft_pos _); convert! (loft_deriv x).div ((loft_deriv x).const_add 1) h.ne' using 1; rw [traces,reverse,descent]; field_simp; ring
lemma trail(x:ℝ):0 < τ x:= mul_pos (mul_pos Real.pi_pos (ball x).1) (ball x).2
lemma rails : StrictMono P:= strictMono_of_deriv_pos (fun x=> by rw [(day x).deriv]; exact trail x) -- needs diff or none
lemma caters : P '' univ=Ioo 0 1:=by
 ext x; constructor
 · rintro ⟨x,h,rfl⟩; exact ⟨(ball x).1, sub_pos.mp (ball x).2⟩
 intro p; rcases p with ⟨e,f⟩; have g:=sub_pos.mpr f
 let q:= x/(1-x); refine ⟨Real.log q /Real.pi,Set.mem_univ _,?_⟩; rw [descent,loft, mul_div_cancel₀ _ Real.pi_pos.ne'] -- tune π comm
 rw [Real.exp_log (show 0< q from div_pos e g)]; unfold q; field_simp; ring

/- Euler left & right exact analytic fares -/
-- φ=1/(2 cosh(π t/2))
def fizz (x:ℝ):= ε (Real.pi*x/2)/(1+loft x)
def fuel (z:ℂ)(x:ℝ):ℂ:= (fizz x:ℂ)*ξ (z*(x:ℂ))
def fare (z:ℂ) :ℂ:=1/2+z/(π:ℂ)
@[fun_prop] lemma fizz_cont : Continuous fizz:= by unfold fizz; apply Continuous.div (by fun_prop) (by fun_prop) (fun x=>(add_pos (by norm_num) (loft_pos x)).ne')
lemma fizz_pos (x:ℝ):0<fizz x:= div_pos (Real.exp_pos _) (add_pos zero_lt_one (loft_pos _))

private lemma elementary (u:ℂ)(a x:ℝ)(h:0<a): (a:ℂ) ^ u=ξ (((Real.log a:ℝ):ℂ)*u):= by rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast h.ne'), Complex.ofReal_log h.le]
def burn (u:ℂ)(x:ℝ):= (x:ℂ)^(u-1)*( (1-x:ℝ):ℂ ) ^((1-u)-1)
lemma fees (z:ℂ)(x:ℝ): |τ x| • burn (fare z) (P x)=(π:ℂ)*fuel z x := by
 let A:= P x; let B:=1-P x; have h:0<A:=(ball x).1; have b:0<B:=(ball x).2; have hp:0<L x:=loft_pos x
 let a:=fare z; let cB:=((Real.log B:ℝ):ℂ); let cA:=((Real.log A:ℝ):ℂ)
 -- exp(cA−cB)=exp(πt)
 have hb:B*L x=A:= by unfold B A; rw [reverse,descent]; ring
 have ht:cA-cB=(π:ℂ)* (x:ℂ):= by unfold cA cB; rw [←Complex.ofReal_sub,← hb, Real.log_mul b.ne' hp.ne',loft,Real.log_exp, ←Complex.ofReal_mul]; congr 1; ring
 rw [abs_of_pos (trail x),burn, elementary _ _ x h, elementary _ _ x b, Complex.real_smul];
 have hy : (A:ℂ) * ξ (cA*(a-1)) = ξ (cA*a):=by rw [mul_sub cA, Complex.exp_sub,mul_one, show ξ cA=(A:ℂ) by rw [show ξ cA= (Real.exp (Real.log A):ℂ) from (Complex.ofReal_exp _).symm,Real.exp_log h]]; field_simp
 unfold traces; change ((π*A*B:ℝ):ℂ)*(ξ (cA*(a-1))*ξ (cB*(1-a-1)))= _
 push_cast; unfold fuel
 rw [show (1:ℂ)-a-1 = -a by ring,mul_neg, show (π:ℂ)*_*_*(ξ (cA*(a-1))*ξ (-(cB*a)))= (π:ℂ)* (B:ℂ)* (A*ξ (cA*(a-1))*ξ (-(cB*a))) from (by ring), hy,← Complex.exp_add,←sub_eq_add_neg,← sub_mul, ht,show (π:ℂ)*(x:ℂ)*a=((Real.pi*x/2:ℝ):ℂ)+z*(x:ℂ) from ?_, Complex.exp_add,← Complex.ofReal_exp]
 swap
 · unfold a fare; push_cast; have hne:(π:ℂ)≠0:=by exact_mod_cast Real.pi_pos.ne'
   field_simp <;> ring
 rw [show fizz x= Real.exp (π*x/2)*B from (by unfold fizz B; rw [reverse]; ring)]; push_cast; ring

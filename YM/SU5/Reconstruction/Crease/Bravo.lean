import YM.SU5.Reconstruction.Crease.Tongs
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Opera
open Function Set Filter MeasureTheory Complex
open scoped BigOperators Topology InnerProductSpace ComplexOrder NNReal ENNReal Complex Real
local notation "πᴿ"=> Real.pi
local notation "π₀" => (Real.pi:ℂ)
def twilight : Set ℝ:= Ioo (-(Real.pi/2)) (Real.pi/2)
lemma fares (z:ℂ)(p:z.re ∈ twilight): (0<(fare z).re)∧ 0<(1-fare z).re:= by
 unfold fare; rw [add_re,sub_re,add_re, div_ofReal_re]; norm_num; rcases p with ⟨b,e⟩; constructor
 · have ht:= (lt_div_iff₀ Real.pi_pos).2 (show (- (1/2:ℝ))*Real.pi < z.re by linarith) -- tune
   linarith
 · linarith [(div_lt_iff₀ Real.pi_pos).2 (show z.re < (1/2:ℝ)*Real.pi by linarith)] -- tune
variable (z:ℂ)(e:z.re∈ twilight)
include e
private lemma integrableB :IntegrableOn (burn (fare z)) (Ioo 0 1):=by
 have u:= (Complex.betaIntegral_convergent (fares z e).1 (fares z e).2).1.mono_set (Ioo_subset_Ioc_self); unfold burn; simpa only [ofReal_sub,ofReal_one] using u
lemma tour : Integrable (fuel z):= by
 have h:= integrableB z e; rw [← caters] at h
 have u:=(integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ (fun x _=>(day x).hasDerivWithinAt) rails.injective.injOn _).1 h -- names
 have he : π₀≠ 0:=ofReal_ne_zero.mpr Real.pi_pos.ne'
 simp_rw [fees] at u; rw [integrableOn_univ, MeasureTheory.integrable_const_mul_iff (isUnit_iff_ne_zero.mpr he)] at u; exact u
lemma firm : (∫ x,fuel z x)= (sin (π₀*fare z))⁻¹:= by
 have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ (fun x _=>(day x).hasDerivWithinAt) rails.injective.injOn (burn (fare z)); simp only [caters,fees,setIntegral_univ, integral_const_mul] at h
 have ht: (∫ x in Ioo (0:ℝ) 1, burn (fare z) x)= betaIntegral (fare z) (1-fare z):= by unfold betaIntegral; rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]; simp only [burn,ofReal_sub,ofReal_one]
 have b:=Gamma_mul_Gamma_eq_betaIntegral (fares z e).1 (fares z e).2; rw [add_sub_cancel _ _,Gamma_one,one_mul, Gamma_mul_Gamma_one_sub] at b -- tune cancel
 exact mul_left_cancel₀ (ofReal_ne_zero.mpr Real.pi_pos.ne') (by rw [← h,ht, ← b,div_eq_mul_inv])
-- sinc nonzero
lemma noPole: sin (π₀*fare z) ≠ 0:=by
 let a:=fare z; have q : Gamma a ≠0 :=Gamma_ne_zero_of_re_pos (fares z e).1; have h : Gamma (1-a)≠0:= Gamma_ne_zero_of_re_pos (fares z e).2
 intro b; apply mul_ne_zero q h; rw [Gamma_mul_Gamma_one_sub]; change _/_= (0:ℂ); rw [show sin (π₀*a)=0 from b,div_zero]

omit e
variable (θ y:ℝ)(hx:θ∈ twilight)
def tune (x:ℝ):ℂ:= exp (x* I)
def spin (θ:ℝ):ℂ:= tune (θ+θ)
def grace (θ:ℝ):ℂ:= tune (-θ) / (2*(Real.cos θ:ℂ))
def cup(θ t:ℝ):ℂ:=(tune (-θ)/2)*fuel θ t
@[fun_prop] lemma cup_cont (θ:ℝ): Continuous (cup θ):= by unfold cup fuel; fun_prop
lemma rhyme(t u:ℝ): tune t*tune u=tune (t+u):= by unfold tune; rw [← exp_add,ofReal_add,add_mul]
lemma melody(t:ℝ):star (tune t)=tune (-t):=by simp [Complex.star_def, tune, ← exp_conj, neg_mul]
lemma tune_norm (t): ‖tune t‖=1:= by simp [tune,norm_exp,mul_re]
lemma tune_not (t):tune t ≠0:=Complex.exp_ne_zero _
include hx
lemma grace_works : (grace θ).re=1/2 ∧ spin θ * grace θ=star (grace θ):= by
 have ht:= Real.cos_pos_of_mem_Ioo hx; have he:tune (-θ)= exp (((-θ:ℝ):ℂ)*I):=rfl
 constructor
 · unfold grace; rw [he,show 2*(Real.cos θ:ℂ)=(((2*Real.cos θ):ℝ):ℂ) from (by push_cast; ring), div_ofReal_re,exp_re]; simp [mul_re,mul_im]; field_simp -- tune
 unfold grace spin; rw [star_div₀,melody,neg_neg,← mul_div_assoc, rhyme]; -- direction
 congr 1 <;> simp [Complex.star_def] -- addition simplified
 rw [← ofReal_cos,Complex.conj_ofReal]
lemma redeem : Integrable (cup θ) := (tour _ (show (θ:ℂ).re ∈ twilight from hx)).const_mul _
lemma receipt : (∫ t:ℝ,cup θ t * tune (t*y)) * (Complex.exp (y:ℂ)+ spin θ* Complex.exp (-(y:ℂ)))=1 := by
 let z := (θ:ℂ)+(y:ℂ)*I
 have hz:z.re∈ twilight:=by simpa [z,mul_re] using hx
 have eh(t:ℝ): cup θ t*tune (t*y)=(tune (-θ)/2)*fuel z t:= by
    unfold cup fuel; rw [show z*t =(θ:ℂ)*t + ( (t*y:ℝ):ℂ)*I from ?_,exp_add]
    swap
    · unfold z; push_cast; ring
    unfold tune; ring -- layout
 let E:=sin (π₀*fare z)
 have h1 : π₀*fare z= z + π₀/2:= by
     unfold fare; have h:π₀≠0:= ofReal_ne_zero.mpr Real.pi_pos.ne'
     field_simp <;> ring
 have h2 : E= cos z:= by unfold E; rw [h1,sin_add_pi_div_two]
 let G:= (exp (y:ℂ)+ spin θ* exp (-(y:ℂ)))
 have hp : tune (-θ) * G = 2* E:= by
    have he : z*I=(θ:ℂ)*I-(y:ℂ):= by simp [z,add_mul,mul_assoc,sub_eq_add_neg]
    unfold G; rw [mul_add,←mul_assoc, h2]; unfold spin; rw [rhyme,show -θ+(θ+θ)=θ by ring]; -- tune
    rw [cos]; unfold tune; rw [← exp_add,← exp_add,ofReal_neg,neg_mul]; -- compare
    rw [he]; ring_nf; rw [mul_comm I z, he,neg_sub, add_comm]; ring_nf
 simp_rw [eh]; rw [integral_const_mul, firm z hz]
 have hE:E≠0:= noPole z hz
 change _ / _ * E⁻¹ * G=_
 field_simp; linear_combination hp
end YM.Opera

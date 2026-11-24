import YM.SU5.FiniteGaugeData.Crest.Laplace
/-! # B-spline generating budget. 
 Constants (symmetric convention). Need ALSO the signed linear-coordinate term at
 these separated distances; grant by exponential multiplier differences, with translation
 one half and legal costs before any subtraction. No assuming derivative of the
 unconsummated Green integral. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Crest
open Function Filter Metric FourierTransform MeasureTheory Set Real
open scoped Topology BigOperators FourierTransform
-- half charge
local notation "φ" => ((1:ℝ)/2)
local notation "I" => Complex.I
def skirt (x:ℝ):ℂ:=sinc (x/2)
def weight (a:ℝ):ℝ:= (Real.exp (a*φ)-Real.exp (-a*φ))/a
lemma halfLaw : 0<φ:=by norm_num
lemma weight_pos {a:ℝ}(h:0<a):0<weight a:= div_pos (sub_pos.mpr (Real.exp_lt_exp.mpr ((mul_lt_mul_of_pos_right (by linarith : -a<a) halfLaw)))) h
@[fun_prop] lemma footCont : Continuous skirt:=by unfold skirt; fun_prop
lemma skirt_area(x:ℝ) : ∫ y in Ioc (-φ) φ, surge y x=skirt x:=by
 rw [← intervalIntegral.integral_of_le (by norm_num : -φ ≤ φ)]
 by_cases he:x=0
 · subst x; norm_num [surge,skirt,Complex.real_smul]
 have hp(y:ℝ):surge y x=Complex.exp (↑(x*y)* Complex.I):=by rw [surge,mul_comm _ x]; congr 1; ring
 simp_rw [hp]; rw [intervalIntegral.integral_comp_mul_left (fun v:ℝ=> Complex.exp ((v:ℂ)*Complex.I)) he,show x*(-φ)=- (x/2) by ring,show x*φ=x/2 by ring, integral_exp_mul_I_eq_sinc, Complex.real_smul]; unfold skirt; push_cast; have hz : (x:ℂ)≠0:=by exact_mod_cast he
 field_simp -- tune
lemma weight_c {a:ℝ} (h:0<a): ∫ y:ℝ in Ioc (-φ) φ, (Real.exp (-a*y):ℂ)=weight a:=by
 have hp: (a:ℂ)≠0:=by exact_mod_cast h.ne'
 simp only [Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_neg]
 rw [← intervalIntegral.integral_of_le (by norm_num:-φ ≤ φ), integral_exp_mul_complex (neg_ne_zero.mpr hp)]; unfold weight; push_cast; rw [neg_mul_neg]; ring

def smoothZip(a:ℝ)(p:ℕ) := fun x:ℝ=> skirt x^p * zip a x
def biasStamp (f:ℝ→ℂ) (x:ℝ) := (-I*x)*f x
lemma patched_norm (x:ℝ) : ‖skirt x‖≤1:=by simpa only [skirt, Complex.norm_real,Real.norm_eq_abs] using abs_sinc_le_one (x/2)
variable {a:ℝ} {p:ℕ} {w:ℝ}(h:0<a)
include h
lemma smooth_paid(p:ℕ) : Integrable (smoothZip a p):= (zip_paid h).bdd_mul (footCont.pow p).aestronglyMeasurable (Eventually.of_forall (fun x=> (norm_pow_le ..).trans ((pow_le_pow_left₀ (norm_nonneg _) (patched_norm x) p).trans_eq (one_pow p)))) -- maybe =
def sponsor (a:ℝ)(p:ℕ):= Real.pi / a * weight a ^ p
lemma lapel (p:ℕ) {w:ℝ} (W:p*φ ≤ w) : integrated (smoothZip a p) w=(sponsor a p * Real.exp (-a*w):ℝ):=by
 induction p generalizing w with
 | zero=>
   have hp:0 ≤ w:=by simpa using W
   rw [show smoothZip a 0=zip a by funext; simp [smoothZip],throughout h,spark]; push_cast; simp [abs_of_nonneg hp,sponsor]
 | succ p ih=>
   let A:= Set.Ioc (-φ) φ
   let S (x y:ℝ):= surge y x * (surge w x * smoothZip a p x);
   have hx: Integrable (uncurry S) ((volume : Measure ℝ).prod (volume.restrict A)):= (surged w (smooth_paid h p)).comp_fst _|>.bdd_mul (surge_cont.comp (continuous_snd.prodMk continuous_fst)).aestronglyMeasurable (Eventually.of_forall (fun x=> (surge_norm ..).le))
   have he(x:ℝ): surge w x * smoothZip a (p+1) x= ∫ y in A,S x y:=by unfold S; rw [integral_mul_const,show (∫ y in A,surge y x)=skirt x from skirt_area x]; unfold smoothZip; rw [pow_succ]; ring
   have hk(y:ℝ)(u:y∈ A): ∫ x:ℝ,S x y= ((sponsor a p*Real.exp (-a*w):ℝ):ℂ)*↑(Real.exp (-a*y)):=by
      have hp: -(1/2:ℝ)<y:= u.1
      rw [←Complex.ofReal_mul, mul_assoc (sponsor ..), ←Real.exp_add, ←mul_add, ←ih (by push_cast at W; linarith:w + y≥ p*φ)]; unfold S integrated; simp_rw [surge_left, mul_assoc]; simp_rw [←mul_assoc (surge y _), mul_comm (surge y _) (surge w _), mul_assoc]
   unfold integrated; simp_rw [he]; rw [integral_integral_swap hx,setIntegral_congr_fun (s:=A) measurableSet_Ioc hk, integral_const_mul]; unfold A; rw [weight_c h, ← Complex.ofReal_mul]; unfold sponsor; rw [pow_succ]; congr 1; ring
omit h in
lemma step_sinc (x:ℝ): -(I*x)*skirt x= -(surge φ x - surge (-φ) x):=by
 by_cases u:x=0
 · subst x; simp [surge]
 have hp: x*Real.sinc (x/2)=2*Real.sin (x/2):=by rw [Real.sinc_of_ne_zero (by exact div_ne_zero u two_ne_zero)]; field_simp
 rw [neg_mul,mul_assoc,skirt,←Complex.ofReal_mul,hp]; unfold surge; push_cast; rw [Complex.sin]; field_simp; ring_nf; rw [Complex.I_sq]; ring -- check formula
-- ∫ (-I)*x*s^p = -∫(s(w+φ)-s(w-φ)), sign
lemma bias_paid(k:ℕ) : Integrable (biasStamp (smoothZip a (k+1))):=by
 let f:= smoothZip a k; refine ((surged (-φ) (smooth_paid h k)).sub (surged φ (smooth_paid h k))).congr ?_
 refine Eventually.of_forall fun i=> ?_; change surge (-φ) i*f i-surge φ i*f i=biasStamp _ i; rw [biasStamp,neg_mul (I),show smoothZip a (k+1) i=skirt i*f i by unfold f smoothZip; rw [pow_succ',mul_assoc],←mul_assoc,step_sinc]; ring
lemma shifted (p:ℕ) {w:ℝ} (W:(p+1:ℕ)*φ ≤ w) : integrated (biasStamp (smoothZip a (p+1))) w=(a * sponsor a (p+1) * Real.exp (-a*w):ℝ):=by
 let f:=smoothZip a p
 have he(x:ℝ):surge w x*biasStamp (smoothZip a (p+1)) x=surge (w-φ) x*f x - surge (w+φ) x*f x:=by rw [sub_eq_add_neg w, surge_left, surge_left]; unfold biasStamp; rw [neg_mul (I), show smoothZip a (p+1) x=skirt x*f x by unfold f smoothZip; rw [pow_succ',mul_assoc],←mul_assoc (-(I*_)),step_sinc]; ring
 unfold integrated; simp_rw [he]; rw [integral_sub (surged _ (smooth_paid h p)) (surged _ (smooth_paid h p))]
 push_cast at W; rw [show (∫ x,surge (w-φ) x*f x)=_ from lapel h p (by linarith: p*φ ≤ w-φ), show (∫ x,surge (w+φ) x*f x)=_ from lapel h p (by linarith: p*φ ≤ w+φ), ←Complex.ofReal_sub, show -a*(w-φ)=-a*w+a*φ by ring, show -a*(w+φ)=-a*w+-a*φ by ring, Real.exp_add, Real.exp_add, show sponsor a (p+1)=sponsor a p*weight a by unfold sponsor; rw [pow_succ,mul_assoc], weight]; congr 1; field_simp -- tune mul_assoc direction
-- negative via geometric
lemma trough (p:ℕ) {w:ℝ} (W:p*φ ≤ w) : integrated (smoothZip a p) (-w)= (sponsor a p * Real.exp (-a*w):ℝ):=by
 rw [← lapel h p W]; unfold integrated; rw [←integral_neg_eq_self (fun x:ℝ=> surge (-w) x* smoothZip a p x) volume]; simp [skirt, surge,smoothZip, (show ∀ x:ℝ, Real.sinc (-x/2) = Real.sinc (x/2) from fun x=>by rw [neg_div,sinc_neg]),zip]
lemma downhill (p:ℕ) {w:ℝ} (W:(p+1:ℕ)*φ ≤ w) : integrated (biasStamp (smoothZip a (p+1))) (-w)= -((a*sponsor a (p+1)*Real.exp (-a*w):ℝ):ℂ):=by
 rw [←shifted h p W]; unfold integrated; rw [←integral_neg_eq_self (fun x:ℝ=> surge (-w) x*biasStamp (smoothZip a _) x) volume, ←integral_neg]; apply integral_congr_ae; refine Eventually.of_forall fun x=>?_; simp [skirt,surge,smoothZip, (show ∀ x:ℝ, Real.sinc (-x/2) = Real.sinc (x/2) from fun x=>by rw [neg_div,sinc_neg]),zip,biasStamp]
end YM.CF.Crest
#print axioms YM.CF.Crest.lapel
#print axioms YM.CF.Crest.shifted
#print axioms YM.CF.Crest.downhill

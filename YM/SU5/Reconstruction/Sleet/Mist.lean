import YM.SU5.Reconstruction.Sleet.Shelter
import YM.SU5.Reconstruction.Seams.Ultralimit
/-! # Gaussian powered charts -/
set_option autoImplicit false
noncomputable section
namespace YM.ConePrice.Storm
open Set Filter MeasureTheory Measure Complex Sail YM.Paley Metric
open scoped Topology NNReal Real Classical

def pearl (z:ℂ):ℂ:= Complex.exp (- z^2)/ (√(Real.pi):ℝ)
def glimmer (x:ℝ):ℝ:= Real.exp (-x^2)/√(Real.pi)
lemma pearl_ignition (z:ℂ): ‖pearl z‖= glimmer z.re * Real.exp (z.im^2):=by
 unfold pearl glimmer; rw [norm_div,norm_exp,Complex.norm_real,Real.norm_of_nonneg (by positivity),Complex.neg_re,pow_two z,mul_re]; rw [show -(z.re*z.re-z.im*z.im)= -z.re^2 + z.im^2 from by ring, Real.exp_add]; ring
lemma pearl_land (x:ℝ):pearl (x:ℂ)=glimmer x:=by unfold pearl glimmer; push_cast; rfl
lemma glimmer_pos(x:ℝ):0≤glimmer x:=by unfold glimmer; positivity
lemma glimmer_ok:Integrable glimmer:=by
 have h:= integrable_exp_neg_mul_sq (b:=1) (by norm_num)
 unfold glimmer; apply Integrable.div_const; simpa using h
lemma glimmer_full:(∫ x,glimmer x)=1:=by
 unfold glimmer; rw [integral_div]
 have hx:0<√(Real.pi):=by positivity
 rw [show (∫ x:ℝ,Real.exp (-x^2)) = _ from ?_, div_self hx.ne']; simpa using integral_gaussian 1

/-- Strip data on halves. No joint hol. -/
structure Gust (d C:ℝ)(F:ℝ→ℂ→ℂ)(G:ℂ→ℝ→ℂ):Prop where
 pos : 0<d
 usable(x:ℝ):AnalyticOnNhd ℂ (F x) (slit d)
 guides(y:ℝ):AnalyticOnNhd ℂ (fun t=>G t y) (slit d)
 rent(x:ℝ):∀ y:ℂ,y∈slit d → ‖F x y‖≤ C
 charge(y:ℝ):∀ x:ℂ,x∈slit d → ‖G x y‖≤ C
 meets (x y:ℝ): F x y=G x y
 comes (y:ℂ)(h:y∈slit d):Continuous fun x=>F x y

variable {F:ℝ→ℂ→ℂ}{G:ℂ→ℝ→ℂ}{d C:ℝ}(κ:Gust d C F G)

def crystal(F:ℝ→ℂ→ℂ)(μ:ℝ)(z v:ℂ):= ∫ t:ℝ,pearl ((t:ℂ)-(μ:ℂ)*z)* F (t/μ) v

def ported(G:ℂ→ℝ→ℂ)(μ:ℝ)(z:ℂ)(v:ℝ):= ∫ t:ℝ,(glimmer t:ℂ) * G ((↑(t/μ):ℂ)+z) v

include κ
lemma crystal_shift(μ:ℝ)(z v:ℂ): crystal F μ z v= ∫ t:ℝ, pearl ((t:ℂ) - μ * z.im * I)* F ((t+μ*z.re)/μ) v:=by
 unfold crystal
 rw [← integral_add_right_eq_self (f:=fun t:ℝ=>pearl ((t:ℂ)-(μ:ℂ)*z)* F (t/μ) v) (μ*z.re)] -- names
 refine integral_congr_ae (ae_of_all _ fun t=>?_)
 simp only
 rw [show ((↑(t+μ*z.re):ℂ)-(μ:ℂ)*z)= (t:ℂ) - μ * z.im * I from ?_]; apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
lemma crystal_stay(μ:ℝ)(z v:ℂ)(e:v∈slit d): ‖crystal F μ z v‖ ≤ C*Real.exp ((μ*z.im)^2):=by
 rw [crystal_shift κ]
 let P(t:ℝ):=pearl ((t:ℂ)- μ * z.im* I)* F ((t+μ*z.re)/μ) v
 let K(t:ℝ):= glimmer t * (C*Real.exp ((μ*z.im)^2))
 have hk:Integrable K:=glimmer_ok.mul_const _
 have hp(t:ℝ): ‖P t‖≤ K t:=by
   unfold P K; rw [norm_mul]; refine (mul_le_mul_of_nonneg_left (κ.rent _ _ e) (norm_nonneg _)).trans_eq ?_; rw [pearl_ignition]; simp [Complex.mul_re,Complex.mul_im]; ring -- casts
 have u: Continuous P:= by unfold P; refine Continuous.mul ?_ ((κ.comes v e).comp (f:=fun t:ℝ=>(t+μ*z.re)/μ) (by fun_prop)); unfold pearl; fun_prop
 have hP: Integrable P:= hk.mono' u.aestronglyMeasurable (ae_of_all _ hp)
 apply (norm_integral_le_integral_norm P).trans ((integral_mono hP.norm hk hp).trans_eq _)
 unfold K; rw [integral_mul_const,glimmer_full,one_mul]
lemma star_dawn(μ:ℝ)(z:ℝ)(v:ℂ)(e:v∈slit d): ‖crystal F μ (z:ℂ) v‖≤ C:=by simpa using crystal_stay κ μ z v e
lemma ported_real(μ:ℝ)(e:μ≠0)(z v:ℝ): crystal F μ (z:ℂ) (v:ℂ)= ported G μ z v:=by
 rw [crystal_shift κ]; unfold ported; refine integral_congr_ae (ae_of_all _ fun x=>?_); -- simp casts
 rw [ofReal_im]; simp only [ofReal_re, ofReal_zero,mul_zero,zero_mul,sub_zero]
 rw [pearl_land,show (x+μ*z)/μ=x/μ+z from by field_simp,κ.meets,Complex.ofReal_add]
lemma ported_ok (μ:ℝ)(z:ℂ)(v:ℝ)(p:z∈slit d) : ‖ported G μ z v‖≤ C:= by
 let Q(x:ℝ):ℂ:= x/μ+z -- addition real divide? coercion
 let K(x:ℝ):= (glimmer x:ℂ) * G (Q x) v
 have ht (x:ℝ):Q x= (↑(x/μ):ℂ)+z:=by unfold Q; push_cast; rfl
 have h(x:ℝ): Q x∈ slit d:=by change |_|<d; rw [ht]; simpa using (show |z.im|<d from p)
 have hk: Continuous K:= by
   unfold K; refine Continuous.mul ?_ ((κ.guides v).continuousOn.comp_continuous ?_ h);
   · unfold glimmer;fun_prop
   · unfold Q;fun_prop
 have H(x:ℝ):‖K x‖≤ glimmer x*C:=by unfold K; rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (glimmer_pos _)]; exact mul_le_mul_of_nonneg_left (κ.charge v _ (h _)) (glimmer_pos _)
 apply (le_of_eq ?_).trans ((norm_integral_le_integral_norm K).trans ((integral_mono (f:= (‖K ·‖)) (( (glimmer_ok.mul_const C).mono' hk.aestronglyMeasurable (ae_of_all _ H)).norm) (glimmer_ok.mul_const _) H).trans_eq ?_))
 · unfold K ported; simp_rw [ht]
 rw [integral_mul_const, glimmer_full,one_mul]
end YM.ConePrice.Storm

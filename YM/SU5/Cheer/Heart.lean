import YM.SU5.Cheer.Spinor
import YM.Mink.Geometry
set_option autoImplicit false
set_option maxHeartbeats 240000
/-! # Weyl-kernel spectrum calculated in regularized sector. Uniform E3 reproductions on real positions; even complex t ! -/
noncomputable section
namespace YM.Cheer
open Function Metric Set Filter Complex GaussianFourier MeasureTheory Measure Mink
open scoped Real Topology NNReal ENNReal InnerProductSpace BigOperators
abbrev SpinTrack:= SpinP × SpinP
local notation "μ"=> (volume : Measure SpinP)
local notation "π'"=> ((Real.pi:ℝ):ℂ)
local notation "Au" p:max=> p (0:SpaceAxis)
local notation "Av" p:max=> p (1:SpaceAxis)
local notation "Aq" p:max=> p (2:SpaceAxis)
def shoal (z:SpinTrack):Space3:=WithLp.toLp 2 (![2*(star z.1*z.2).re, 2*(star z.1*z.2).im, bill z.1 - bill z.2])
def apex (z:SpinTrack):E4:=Mink.divide.symm (shoal z,bill z.1+bill z.2)
def lane (p:Space3):ℂ:= ⟨Au p,Av p⟩
lemma expense (z w:Space3) : inner ℝ z w = Au z*Au w+Av z*Av w+Aq z*Aq w:=by simp [PiLp.inner_apply, Fin.sum_univ_succ,SpaceAxis]; ring
lemma rates (p:Space3) : ‖p‖^2=Au p^2+Av p^2+Aq p^2:=by rw [←real_inner_self_eq_norm_sq,expense]; ring
@[simp] lemma pierT(z:SpinTrack): time (apex z)=bill z.1+bill z.2:=by exact time_position (shoal z) (bill z.1+bill z.2)
@[simp] lemma pierS(z:SpinTrack): spatial (apex z) = shoal z:=spatial_position ..
@[simp] lemma raw_u(z:SpinTrack): Au (shoal z)=2*(star z.1*z.2).re:=rfl
@[simp] lemma raw_v(z:SpinTrack): Av (shoal z)=2*(star z.1*z.2).im:=rfl
@[simp] lemma raw_q(z:SpinTrack): Aq (shoal z)=bill z.1 - bill z.2:=rfl
@[fun_prop] lemma valid_shoal: Continuous shoal:= by
 change Continuous ( (WithLp.toLp 2) ∘ (fun v=> (shoal v).ofLp)); refine (PiLp.continuous_toLp ..).comp (continuous_pi (fun i=>?_)); fin_cases i <;> simp only [raw_u,raw_v,raw_q] <;> fun_prop
@[fun_prop] lemma valid_apex: Continuous apex:=by unfold apex; fun_prop
lemma pearl_value (p:SpinP): bill p=p.re^2+p.im^2:=by rw [bill, ← Complex.normSq_eq_norm_sq]; simp [pow_two,normSq_apply]
lemma depth (v u:ℂ) (p:Space3): (star u*v).re*Au p + (star u*v).im* Av p= inner ℝ (lane p*u) v:=by
 rw [Complex.inner]; simp [lane,Complex.mul_re,Complex.mul_im]; ring
section
variable (p:Space3) (T:ℂ) (u v:SpinP)
def cab :ℂ :=T+(Aq p:ℂ)*I
local notation "ξ"=> cab p T
local notation "ζ"=> T-(Aq p:ℂ)*I
def wind := ((T^2+(‖p‖:ℂ)^2))
def wing := wind p T / ξ
lemma lane_fee : ((bill (lane p):ℂ))+(Aq p:ℂ)^2=(‖p‖:ℂ)^2:= by rw [← ofReal_pow ‖p‖ 2,rates,pearl_value]; unfold lane; push_cast; rfl
lemma legato : wind p T= ζ*ξ + bill (lane p) := by rw [wind,← lane_fee]; unfold cab; ring_nf; simp [I_sq]
lemma costs_wing : 0<T.re → 0< (wing p T).re:=by
 intro h; have hp: 0 < (ξ).re:=by simpa [cab] using h
 have ht:0 ≤ ((ξ)⁻¹).re:= by rw [inv_re]; exact div_nonneg hp.le (normSq_nonneg _)
 have he:wing p T= ζ + ↑(bill (lane p)) * (ξ)⁻¹ := by rw [wing,legato,add_div]; field_simp [ne_of_real_pos hp]
 rw [he]; simp only [inv_re] at ht; simp; exact add_pos_of_pos_of_nonneg h (mul_nonneg (bill_p _) ht)
lemma wind_ne : 0<T.re → wind p T≠0 := fun h=>by intro b; have ht:= costs_wing p T h; simp [wing,b] at ht
-- kernel = ∫ mu and product
def warmK (p:Space3)(T:ℂ)(z: SpinTrack):ℂ:=cexp ((inner ℝ (shoal z) p:ℂ)*I - T*(time (apex z):ℂ))
def lightK (p:Space3)(T:ℂ)(z: SpinTrack):ℂ:=(bill z.1:ℂ) * warmK p T z
lemma warmAt : warmK p T (u,v)= pearl (ζ) u * cexp (-(ξ)*(‖v‖:ℂ)^2+(2*I)*(inner ℝ (lane p*u) v:ℂ)):=by
 unfold warmK pearl; rw [←Complex.exp_add,pierT,expense,raw_u,raw_v,raw_q,← depth]
 simp only; unfold cab; rw [← ofReal_pow ‖v‖, show ‖v‖^(2:ℕ)= bill v from rfl]
 push_cast; ring_nf
lemma priceK (z:SpinTrack): ‖lightK p T z‖ = ‖bevel T z.1‖ * ‖pearl T z.2‖:= by
 rcases z with ⟨u,v⟩; rw [lightK,warmK,bevel]; simp only [norm_mul, Complex.norm_exp, pearl_norm,pierT]; simp only [Complex.ofReal_add, sub_re, I_re, I_im, ofReal_im, mul_re, add_re, add_im, ofReal_re, add_zero, zero_mul, mul_zero, sub_zero,zero_sub]; rw [mul_assoc,← Real.exp_add]; congr 2 <;> ring
variable {T}
variable (h:0<T.re)
include h
lemma merit : Integrable (lightK p T) ((μ).prod μ):= by
 refine ⟨(show Continuous (lightK p T) by unfold lightK warmK; fun_prop).aestronglyMeasurable, (hasFiniteIntegral_norm_iff _).mp ?_⟩
 simp_rw [priceK]; exact ( (bevel_gift h).1.norm.mul_prod (pearl_paid h).norm).2
lemma pair_buy : (∫ v:SpinP, lightK p T (u,v)) = (π' / ξ) * bevel (wing p T) u:=by
 have he:0<(ξ).re:= by simpa [cab] using h
 have hb:ξ ≠ 0:= ne_of_real_pos he
 simp_rw [lightK, warmAt]; simp only [integral_const_mul]; rw [integral_cexp_neg_mul_sq_norm_add he]; rw [show Module.finrank ℝ SpinP=2 from Complex.finrank_real_complex]; norm_num only [Nat.cast_ofNat, Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_zero, div_self, Complex.cpow_one]
 simp only [bevel,pearl]
 let w:= (2*I)^2* (‖lane p*u‖:ℂ)^2 / (4*ξ); let z:=cexp (-(bill u:ℂ)* (ζ) + w); have ht: w= - ↑(bill (lane p)) * ↑(bill u)/ ξ := by
    unfold w; rw [show (‖lane p * u‖:ℂ)^ (2:ℕ)=(bill (lane p*u):ℂ) from (ofReal_pow ..).symm, mul_pow, I_sq, bill_m,ofReal_mul]; ring
 calc _ = ↑(bill u) * (π' / ξ) * z := by dsimp only [z]; rw [Complex.exp_add]; ring
      _ = _:= by rw [show z= cexp (-(bill u:ℂ)*wing p T) by unfold z; rw [ht]; congr 1; rw [wing,legato]; field_simp; ring]; ring
lemma both_buy : (∫ z, lightK p T z ∂ ((μ).prod μ))= (π'^2*ξ /(wind p T)^2):= by
 rw [integral_prod _ (merit p h)]; simp_rw [pair_buy _ _ h]; rw [integral_const_mul, (bevel_gift (costs_wing p T h)).2]; rw [wing]; field_simp [ne_of_real_pos (show 0 < (ξ).re by simpa [cab] using h),wind_ne p T h]
end
end YM.Cheer
#print axioms YM.Cheer.both_buy

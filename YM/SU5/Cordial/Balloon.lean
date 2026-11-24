import YM.Heat.Duration
import YM.OS.Core
/-! # Cost for varying pairings on zooming time scale. Spectral calculus on SAME heat flow. -/
set_option autoImplicit false
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter MeasureTheory Measure Spectral Complex Analysis Boundary Probe
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators
namespace Balloon
variable {H : Hilbert} {a : Axis} (S : Semigroup H a)
noncomputable def tinct (a:Axis)(t:ℝ≥0)(x:E4) := Real.exp (-((t:ℝ)*x a))
variable (t u:ℝ≥0)(x:Cross a)(y:H)
local notation "μ"=> S.ℚmeasure.diagonal y
lemma fuel(c:E4) (p:0 ≤ c a) : tinct a t c≤1:= Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg t.property p))
lemma admitted : Integrable (tinct a t) μ:= by
 apply (integrable_const («μ»:= μ) (1:ℝ)).mono' (show AEStronglyMeasurable (tinct a t) μ from (show Continuous (tinct a t) by unfold tinct; fun_prop).aestronglyMeasurable)
 filter_upwards [S.bright y] with z h; rw [Real.norm_of_nonneg (show 0≤tinct a t z from (Real.exp_pos _).le)]; exact fuel t z h
lemma during : inner ℂ y (S.U x (S.E t y))= ∫ c, plane c (x:E4)* (↑(tinct a t c):ℂ) ∂μ := by
 let z:=Complex.I*(t:ℝ); have hw:x.val a=0:= x.property; let P' :=↑(t:ℝ); have hz:z.im=(t:ℝ):=by simp [z];
 have h : S.J x y y z=inner ℂ y (S.U x (S.E t y)):= by
   unfold J ray unit
   simp only [ContinuousLinearMap.comp_apply,hw]; rw [show SEP a x=x from ?_, show z.re=0 by simp [z], S.birth,hz,Real.toNNReal_coe]; rfl
   exact Subtype.ext (show (x:E4) - (x.val a) • basis a= (x:E4) by rw [hw,zero_smul,sub_zero]);
 rw [← h, heat _ _ y (show z∈Paley.high from (show 0≤ z.im from hz.symm ▸ t.property))]; apply integral_congr_ae (ae_of_all _ fun x=>?_) -- syntax `apply term` with hole?
 congr 1
 rw [show (x a:ℂ)* z * I= ↑(-((t:ℝ)*(x a))) by unfold z; push_cast; ring_nf; simp [I_sq], ←ofReal_exp]; rfl
lemma earthy : (inner ℂ y (S.E t y)).re= ∫ c, tinct a t c ∂μ :=by
 have h:= during S t 0 y; rw [S.uZero,ContinuousLinearMap.id_apply] at h; simp only [ZeroMemClass.coe_zero,plane,inner_zero_right,ofReal_zero,zero_mul,Complex.exp_zero,one_mul] at h
 rw [h, integral_complex_ofReal]; rfl
lemma wool : (inner ℂ (S.E t y) (S.E u y)).re= ∫ c, tinct a (t+u) c ∂μ := by rw [S.swing,← ContinuousLinearMap.comp_apply,←S.time]; exact earthy S _ _ -- direction
lemma costp : ‖S.E t y‖^2=∫ c, tinct a (t+t) c ∂ μ:=by rw [← wool]; exact (inner_self_eq_norm_sq (𝕜:=ℂ) _).symm
lemma tint_add (p:E4): tinct a (t+u) p=tinct a t p*tinct a u p:=by simp [tinct,add_mul,Real.exp_add]; ring
lemma distanceE : ‖S.E t y-S.E u y‖^2=∫ c, (tinct a t c-tinct a u c)^2 ∂μ:= by
 rw [norm_sub_sq (𝕜:=ℂ),costp,costp,show RCLike.re (inner ℂ _ _) = _ from wool S t u y,←integral_const_mul,←integral_sub (admitted ..) ((admitted S (t+u) y).const_mul _),←integral_add (f:=(fun c=> tinct a (t+t) c-2*tinct a (t+u) c)) (g:=(fun c=>tinct a (u+u) c)) ((admitted S (t+t) y).sub ((admitted S (t+u) y).const_mul _)) (admitted S _ _)]; apply integral_congr_ae (ae_of_all _ fun x=>?_); simp only [tint_add]; ring
section numeric
variable {w s a z:ℝ}
private lemma pop (_u:0 < s)(_e:0 ≤w): s*(w*Real.exp (-s*w)) ≤ 1 := by
 rw [← mul_assoc]; let x:=s*w; rw [← neg_mul_eq_neg_mul]; change x * Real.exp (-x) ≤ 1; rw [Real.exp_neg,←div_eq_mul_inv]; apply div_le_one_of_le₀ (by linarith [Real.add_one_le_exp x]) (Real.exp_pos x).le
private lemma airy (u:0 < a)(v:a≤ s)(p:s≤z)(e:0≤w): Real.exp (-(s*w))-Real.exp (-(z*w)) ≤ (z-s)/a:= by
 let y:= z-s; have hY:0 ≤y:=sub_nonneg.mpr p; let f:=Real.exp (-(s*w)); let g:=Real.exp (-(z*w))
 have he:=Real.one_sub_le_exp_neg (y*w); have h0:0≤ f:= (Real.exp_pos _).le; have hg:g=f*Real.exp (-(y*w)):= by unfold g f; rw [←Real.exp_add]; congr 1; unfold y; ring
 have W:=pop (u.trans_le v) e; rw [neg_mul] at W
 change f-g ≤ y/a; have ht: a*(w*f) ≤ 1:= (mul_le_mul_of_nonneg_right v (mul_nonneg e h0)).trans W
 have hx: f-g ≤ y*(w*f):= calc
     _ ≤ f-f*(1-y*w):=sub_le_sub_left (hg ▸ mul_le_mul_of_nonneg_left he h0) f
     _ = _:=by ring
 apply hx.trans; apply (le_div_iff₀ u).mpr; calc
    _ = y*(a*(w*f)):=by ring
    _ ≤ y*1:= by gcongr
    _ =_:=mul_one y
end numeric
lemma damper (f:ℝ)(p:0<f)(h:f≤t)(g:f≤u)(c:E4)(v:0≤c a) : (tinct a t c-tinct a u c)^2≤(|(t:ℝ)-(u:ℝ)|/f)^2:=by
 have hx:0 ≤ |(t:ℝ)-(u:ℝ)|/f:=by positivity
 refine (sq_abs (tinct a t c-tinct a u c)) ▸ pow_le_pow_left₀ (abs_nonneg _) ?_ 2
 rw [abs_le]; have ht(w z:ℝ≥0)(h:f ≤ w)(g:f≤z) (v0:z≤w):0≤ tinct a z c - tinct a w c:= by
    apply sub_nonneg.mpr (Real.exp_le_exp.mpr ?_); gcongr
 rcases le_total t u with h'|h'
 · rw [abs_sub_comm (t:ℝ),abs_of_nonneg (sub_nonneg.mpr (show (t:ℝ) ≤ u from h'))] at *
   exact ⟨by linarith [ht u t g h h'], airy p h h' v⟩
 have hX:=airy p g (show (u:ℝ) ≤ t from h') v; rw [abs_of_nonneg (sub_nonneg.mpr (show (u:ℝ) ≤ t from h'))] at *; change tinct a u c-tinct a t c≤_ at hX; exact ⟨by linarith,by linarith [ht t u h g h']⟩
lemma real_univ : (μ).real univ=‖y‖^2:= by rw [S.ℚmeasure.same MeasurableSet.univ y,(S.ℚmeasure).all]; rfl
lemma shrinking (f:ℝ)(p:0<f)(h:f≤ t)(g:f≤u): ‖S.E t y-S.E u y‖≤(|(t:ℝ)-(u:ℝ)|/f)*‖y‖:=by
 let V:=|(t:ℝ)-(u:ℝ)|/f; apply le_of_sq_le_sq _ (mul_nonneg (div_nonneg (abs_nonneg _) p.le) (norm_nonneg _)); rw [mul_pow,distanceE];
 have he : (∫ x:E4,(tinct a t x - tinct a u x)^2 ∂ μ)≤ ∫ _:E4,(V^2) ∂μ:= by
    apply integral_mono_ae _ (integrable_const _) ((S.bright y).mono fun x h=>damper t u f p (by assumption) (by assumption) x h) -- shadow
    simp_rw [show ∀ x:E4, (tinct a t x - tinct a u x)^2=tinct a (t+t) x-2*tinct a (t+u) x+tinct a (u+u) x from (by intro x; rw [tint_add,tint_add,tint_add]; ring)]; exact ((admitted S (t+t) y).sub ((admitted S (t+u) y).const_mul _)).add (admitted S (u+u) y)
 refine he.trans_eq ?_; rw [integral_const,real_univ]; exact mul_comm ..
section scaling
variable {r : ℕ→ℝ}{P Q: ℕ→ ℝ≥0}{x:ℝ}(X:ℕ→H)(v:∀ i,0<r i)(p:Tendsto (fun i=>(P i:ℝ)/ r i) atTop (𝓝 x))(q:Tendsto (fun i=>(Q i:ℝ)/ r i) atTop (𝓝 x)) (hp: 0<x)
-- useful version no sequence required along OTHER axis
include v p q
private lemma linear_proj : Tendsto (fun i=> |(P i:ℝ)-(Q i:ℝ)|/(r i*(x/2))) atTop (𝓝 0):= by
 have h:= (p.sub q).abs.div_const (x / 2); rw [sub_self,abs_zero,zero_div] at h; exact h.congr fun i=>by rw [div_mul_eq_div_div,←sub_div,abs_div,abs_of_pos (v i)]
include hp
lemma uniform_price (z:ℝ) (e:ℝ) (t:0<e) : ∀ᶠ i:ℕ in atTop,∀ y:H, ‖y‖ ≤ z → ‖S.E (P i) y - S.E (Q i) y‖ ≤ e:= by
 let k(i:ℕ):= r i*(x/2); have h0:= (linear_proj v p q).mul_const z; rw [zero_mul] at h0
 filter_upwards [h0.eventually (ge_mem_nhds t), p.eventually (le_mem_nhds (half_lt_self hp)),q.eventually (le_mem_nhds (half_lt_self hp))] with i h u f y w
 have hv:k i≤ (P i:ℝ):= (mul_comm ..).le.trans ((le_div_iff₀ (v i)).1 u); have he:k i ≤ (Q i:ℝ):= (mul_comm ..).le.trans ((le_div_iff₀ (v i)).1 f)
 have ht:0<k i:=mul_pos (v i) (half_pos hp); exact (shrinking S _ _ y (k i) ht hv he).trans ((mul_le_mul_of_nonneg_left w (by positivity)).trans h)
lemma uniform_zoom (h:∃ z:ℝ,∀ᶠ i in atTop,‖X i‖ ≤ z): Tendsto (fun i=> S.E (P i) (X i) - S.E (Q i) (X i)) atTop (𝓝 0):= by
 rw [tendsto_zero_iff_norm_tendsto_zero]; apply Metric.tendsto_nhds.mpr; rintro ε t; obtain ⟨z,h⟩:=h
 filter_upwards [uniform_price S v p q hp z (ε/2) (half_pos t), h] with i e hi; simpa using lt_of_le_of_lt (e (X i) hi) (half_lt_self t)
end scaling
end Balloon
end YM.OS.Semigroup
#print axioms YM.OS.Semigroup.Balloon.uniform_zoom

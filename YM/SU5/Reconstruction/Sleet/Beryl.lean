import YM.SU5.Reconstruction.Sleet.Flurry
import Mathlib.Analysis.Complex.Hadamard
/-! # Real lines and enough width. Purchase without assuming joint extension. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConePrice.Storm
open Set Filter Complex Sail Metric HadamardThreeLines
open scoped Topology NNReal Real Classical
variable {F:ℝ→ℂ→ℂ}{G:ℂ→ℝ→ℂ}{d C:ℝ}(κ:Gust d C F G)
def chamber (d:ℝ)(x y:ℂ):= |x.im|+|y.im|<d
lemma chamber.south {d:ℝ}{x y:ℂ}(p:chamber d x y): x∈ slit d:= by unfold chamber at p; change |x.im|<d; linarith [abs_nonneg y.im]
lemma chamber.north {d:ℝ}{x y:ℂ}(p:chamber d x y): y∈ slit d:= by unfold chamber at p; change |y.im|<d; linarith [abs_nonneg x.im]
include κ
lemma middle_power(μ:ℝ)(hm:μ≠0)(x y:ℂ)(w:chamber d x y): ‖crystal F μ x y‖≤ C:=by
 have hp:= w.north; have hq:=w.south; unfold chamber at w
 by_cases hg:x.im=0
 · exact (Eq.trans_le (congr_arg (fun x=>‖crystal F μ x y‖) (show x = (x.re:ℂ) from Complex.ext (by simp) (by simp [hg]))) (star_dawn κ μ _ _ hp))
 by_cases ha:y.im=0
 · exact (Eq.trans_le (congr_arg (fun y=>‖crystal F μ x y‖) (show y=(y.re:ℂ) from Complex.ext (by simp) (by simp [ha]))) (by rw [ported_crown κ μ hm x hq]; exact ported_ok κ μ x _ hq))
 let s:=|x.im|+|y.im|; let t:= |x.im|/s; have hx:0< |x.im|:=abs_pos.mpr hg; have hy:0< |y.im|:=abs_pos.mpr ha; have hs:0<s:=add_pos hx hy; have ht:0<t:=div_pos hx hs; have hu:t<1:= (div_lt_one hs).mpr (by unfold s;linarith); have uv:0<1-t:=by linarith
 let b:= x.im/t; let a:=y.im/(1-t); have hb:b*t=x.im:=div_mul_cancel₀ _ ht.ne'; have hk:a*(1-t)=y.im:=div_mul_cancel₀ _ uv.ne'
 have w₁:|b|=s:=by unfold b; rw [abs_div,abs_of_pos ht]; unfold t; field_simp
 have w₂:|a|=s:=by unfold a; rw [abs_div,abs_of_pos uv]; apply (div_eq_iff uv.ne').2; rw [mul_sub, mul_one,show s*t = |x.im| from (by unfold t;field_simp)]; unfold s;ring
 let X(z:ℂ):= (x.re:ℂ)+(b:ℂ)*z*I; let Y(z:ℂ):=(y.re:ℂ)+(a:ℂ)*(1-z)*I
 have hX(z): (X z).im=b*z.re:=by simp [X,mul_im,mul_re]
 have hY(z): (Y z).im=a*(1-z.re):=by simp [Y,mul_im,mul_re] -- indent
 let f(z:ℂ):= crystal F μ (X z) (Y z); let S:= verticalClosedStrip 0 1
 have ch(z:ℂ)(v:z∈S): chamber d (X z) (Y z):= by
    obtain ⟨x1,x2⟩:= (show 0≤ z.re∧ z.re≤1 from v); unfold chamber; rw [hX,hY,abs_mul,abs_mul,w₁,w₂,abs_of_nonneg x1,abs_of_nonneg (by linarith:0≤1-z.re)]; nlinarith only [show s<d from w]
 have h(z:ℂ)(v:z∈ S):AnalyticAt ℂ f z:= by
    let U:= Y ⁻¹' slit d; have hr: IsOpen U:=(slit_open d).preimage (by unfold Y;fun_prop)
    apply crystal_turn κ μ hr (fun _ h=>h) _ _ z (ch z v).north <;> intro z Z <;> first| unfold X;fun_prop | unfold Y;fun_prop
 have hh(t:ℂ): t.re=0 → ‖f t‖≤ C:=by
    intro v; have hz: X t = ((X t).re:ℂ):=Complex.ext (by simp) (by simp [hX,v])
    unfold f; rw [hz]; exact star_dawn κ μ _ _ ((ch t (show t∈S from by unfold S verticalClosedStrip; simp [v])).north)
 have hf(t:ℂ): t.re=1 → ‖f t‖≤ C:=by
    intro v; have hz: Y t = ((Y t).re:ℂ):=Complex.ext (by simp) (by simp [hY,v])
    have hv: t∈S:= by unfold S verticalClosedStrip; simp [v]
    unfold f; rw [hz,ported_crown κ μ hm _ (ch t hv).south]; exact ported_ok κ μ _ _ (ch t hv).south
 have C₀:0≤C:=le_trans (norm_nonneg _) (hh 0 (by simp))
 have hv : BddAbove ((norm∘f) '' S):= by
    refine ⟨C*Real.exp (μ^2*d^2),?_⟩; rintro _ ⟨z,hS,rfl⟩; apply (crystal_stay κ μ (X z) (Y z) (ch z hS).north).trans
    rw [mul_pow]; gcongr C*Real.exp (_*?_); nlinarith [show |(X z).im|<d from (ch z hS).south,mul_self_le_mul_self (abs_nonneg (X z).im) (show |(X z).im|≤ d from (show |(X z).im|< _ from (ch z hS).south).le),abs_mul_abs_self (X z).im]
 have H:= norm_le_interp_of_mem_verticalClosedStrip₀₁' f (show (t:ℂ)∈ S from ⟨ht.le,hu.le⟩) ⟨(fun z (v:z.re∈Ioo 0 1)=> (h z ⟨v.1.le,v.2.le⟩).differentiableAt.differentiableWithinAt),by rw [verticalStrip,closure_preimage_re,closure_Ioo (by norm_num)]; intro z hg; exact (h z hg).continuousAt.continuousWithinAt⟩ hv hh hf
 rw [ofReal_re,← Real.rpow_add_of_nonneg C₀ uv.le ht.le,sub_add_cancel, Real.rpow_one] at H; unfold f at H
 rw [show X t=x from Complex.ext (by simp [X,mul_re,mul_im]) (by rw [hX]; exact hb),show Y t=y from Complex.ext (by simp [Y,mul_re,mul_im]) (by rw [hY]; exact hk)] at H; exact H -- supply hb explicitly
end YM.ConePrice.Storm

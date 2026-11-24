import YM.CF.Vp929.Analysis.Gallop
set_option autoImplicit false
set_option maxHeartbeats 440000
noncomputable section
namespace YM.CF.VolumeRate
open Metric Function Topology Set Complex Complex.HadamardThreeLines
variable {w a s b B :ℝ}
/- Logarithmic interpolation off the real diameter using a scaled signed Joukowski annulus. -/
-- on ball 4a. Real on |x|≤2a. ‖target‖= t≤a. take r≥1 with r-r^-1=t/a.
private def scarf (a:ℝ)(d:ℝ)(z:ℂ):= (d:ℂ)*(a:ℂ)*(exp z+(exp z)⁻¹)
private lemma penn (hs: |s|≤a)(ha:0<a): ∃ d t:ℝ, |d|=1 ∧ t≥1∧ t ≤ 2 ∧ Real.log t≤ |s|/a ∧ scarf a d (log ((t:ℂ)*I))= I*s:=by
 -- solve monotone or quadratic. d real sign. t=a0+sqrt(1+a0²)
 let u:=|s|/a; have h:0≤u:=by unfold u; positivity
 have hl : u ≤ 1:= (div_le_one ha).mpr hs
 let v:=Real.sqrt (1+(u/2)^2); have hv:0≤v:=Real.sqrt_nonneg _; have hi: v^2=1+(u/2)^2:=Real.sq_sqrt (by positivity); let t:= u/2+v; have hp:t*t-u*t-1=0:=by unfold t; nlinarith
 have hp':1≤ t:= by unfold t; nlinarith
 have hx:t≤1+u:=by nlinarith
 have hh:t≤2:=by linarith
 let d:ℝ:= if 0≤s then 1 else -1
 have e:t≠0:=by linarith
 have hx':d*|s|=s:=by
    unfold d; split; next h=> rw [abs_of_nonneg h,one_mul]
    next h=> rw [abs_of_nonpos (le_of_not_ge h),neg_one_mul,neg_neg]
 have hy: t-t⁻¹=u:=by field_simp; nlinarith
 refine ⟨d,t,(by unfold d; split<;>simp),hp',hh,(Real.log_le_sub_one_of_pos (by linarith)).trans (by unfold u at hx; linarith),?_⟩
 calc
   _ = (d:ℂ)*(a:ℂ)* (I*(t-t⁻¹:ℝ)):=by unfold scarf; rw [exp_log (mul_ne_zero (Complex.ofReal_ne_zero.mpr e) I_ne_zero),mul_inv_rev]; simp; ring_nf; simp
   _ = _:=by
            rw [hy]; have U':d*a*u=s:= by unfold u; field_simp; nlinarith
            rw [←U', ofReal_mul, ofReal_mul]; ring
-- exponent on log savings O(|s|/a)
lemma off_line {f:ℂ→ℂ}(a:ℝ)(h:0<a)(s:ℝ)(p:|s|≤a)(c:b≤B)(ht:DifferentiableOn ℂ f (ball 0 (5*a)))(u:∀ x∈ ball (0:ℂ) (5*a),‖f x‖ ≤ Real.exp B)(w:∀ x:ℝ,|x|≤2*a→ ‖f x‖ ≤ Real.exp b):
 ‖f (I*s)‖ ≤ Real.exp (b+(B-b)*|s|/a / Real.log 3):=by
 obtain ⟨d,t,e,j,k,I₀,H⟩:=penn p h; let G:= f ∘ scarf a d; have hz:(0:ℝ)< Real.log 3:= Real.log_pos (by norm_num); let Z:= verticalClosedStrip 0 (Real.log 3); let z:= log ((t:ℂ)*I)
 have hv (s) (p:s∈Z) : scarf a d s∈ ball (0:ℂ) (5*a):= by
    let y:= exp s; have hx:1≤‖y‖:= by rw [show ‖y‖=Real.exp s.re from norm_exp s]; exact Real.one_le_exp p.1
    have hh:‖y‖ ≤ 3:= (norm_exp s).trans_le ((Real.exp_monotone p.2).trans_eq (Real.exp_log (by norm_num)))
    apply mem_ball_zero_iff.mpr; unfold scarf; simp only [norm_mul,norm_real,Real.norm_eq_abs,e,one_mul,abs_of_pos h]; have ht:= (norm_add_le y y⁻¹).trans (add_le_add hh (show ‖y⁻¹‖≤ 1 by rw [norm_inv]; exact inv_le_one_of_one_le₀ hx)); nlinarith
 have R:DifferentiableOn ℂ G Z:= ht.comp (Differentiable.differentiableOn (show Differentiable ℂ _ from ((differentiable_exp.add (differentiable_exp.inv exp_ne_zero)).const_mul ((d:ℂ)*(a:ℂ))))) hv
 have hG(s)(p:s∈Z): ‖G s‖≤ Real.exp B:=u _ (hv s p)
 have c1(s:ℂ)(hs:s.re=0): ‖G s‖ ≤ Real.exp b:=by
    let y:= d*a*(2*(exp s).re); have ht:‖exp s‖=1:=by rw [norm_exp,hs,Real.exp_zero]
    rw [show G s=f y from ?_]; swap; · unfold G comp scarf y; rw [inv_eq_conj ht, add_conj]; push_cast; congr 1
    apply w; unfold y; have hp:= (abs_re_le_norm (exp s)).trans_eq ht; rw [abs_mul,abs_mul,abs_mul,e,abs_of_pos h,one_mul,abs_of_pos zero_lt_two]; nlinarith
 have h2(s:ℂ)(p:s.re=Real.log 3): ‖G s‖≤Real.exp B:= hG s (by change _ ≤ _ ∧ _; rw [p]; exact ⟨hz.le,rfl.le⟩)
 have he:z.re=Real.log t:=by unfold z; rw [log_re,norm_mul,norm_real,norm_I,mul_one,Real.norm_eq_abs,abs_of_pos (by linarith)]
 have hc : closure (verticalStrip 0 (Real.log 3)) ⊆ Z:= closure_minimal (preimage_mono Ioo_subset_Icc_self) (isClosed_Icc.preimage continuous_re)
 have hg:= norm_le_interp_of_mem_verticalClosedStrip' hz (f:=G) (show z∈ Z from by change z.re∈ Icc _ _; rw [he]; exact ⟨Real.log_nonneg j,Real.log_le_log (by linarith) (by linarith)⟩) ⟨R.mono (preimage_mono Ioo_subset_Icc_self),R.continuousOn.mono hc⟩ (show BddAbove ((norm ∘ G) '' Z) from ⟨_,forall_mem_image.mpr hG⟩) c1 h2
 change ‖f (scarf a d z)‖ ≤ _ at hg; rw [H,← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, sub_zero, sub_zero,he] at hg
 refine hg.trans (Real.exp_monotone ?_); have P:= (mul_le_mul_of_nonneg_left I₀ (sub_nonneg.mpr c)); have e:0<t:=by linarith
 field_simp at *; nlinarith
end YM.CF.VolumeRate

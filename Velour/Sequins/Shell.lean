import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
namespace YM.Velour

open Set Filter Bornology Complex Metric
open scoped Topology


/-- Uniqueness at the edge, no tangential differentiability.
Local maximum argument tested against a quadratic exponential. -/
lemma hem_identical {f:ℂ→ℂ}
    (h:ContinuousOn f {z:ℂ | 0 ≤ z.im})
    (q:AnalyticOnNhd ℂ f {z:ℂ | 0 < z.im})
    {r:ℝ}(p:0<r)(u:∀ x:ℝ, |x| ≤ r → f (x:ℂ)=0):
    ∀ z:ℂ, 0<z.im → f z=0:=by
 let U:= {z:ℂ|0<z.im} ∩ ball 0 r
 have o:IsOpen U:=(isOpen_lt continuous_const Complex.continuous_im).inter isOpen_ball
 have b:IsBounded U:=isBounded_ball.subset inter_subset_right
 let V:= {z:ℂ|0 ≤z.im} ∩ closedBall 0 r
 have g:closure U ⊆ V:=closure_minimal
       (inter_subset_inter (fun z t=>(show 0<z.im from t).le) ball_subset_closedBall)
       ((isClosed_le continuous_const Complex.continuous_im).inter isClosed_closedBall)
 have c:ContinuousOn f (closure U):= h.mono (g.trans inter_subset_left)
 obtain ⟨C,k⟩:= b.isCompact_closure.exists_bound_of_continuousOn c
 let F(z:ℂ):=(r:ℂ)*r-z*z+(r+r:ℝ)*I*z
 have a:AnalyticOnNhd ℂ F univ:=fun _ _=>
       (analyticAt_const.sub (analyticAt_id.mul analyticAt_id)).add (analyticAt_const.mul analyticAt_id)
 have hpow(z:ℂ)(v:‖z‖=r)(p:0≤z.im) : (F z).re ≤0:=by

    have t: r*r=z.re*z.re+z.im*z.im:=by rw [←v, ← sq,Complex.sq_norm,normSq_apply]
    have y:=mul_le_mul_of_nonneg_right ((le_abs_self _).trans ((abs_im_le_norm z).trans_eq v)) p
    simp only [F,mul_re,mul_im,I_im,I_re,add_re,sub_re,ofReal_re,ofReal_im]
    nlinarith only [t,y]
 have l(t:ℝ)(u':0<t)(z:ℂ)(e:z∈U):
    ‖f z‖*Real.exp (t*(F z).re) ≤ C:=by
    let J(w:ℂ):= cexp ((t:ℂ)*F w)
    have A:AnalyticOnNhd ℂ J univ:=fun w hw=> (analyticAt_const.mul (a w hw)).cexp
    have B:DiffContOnCl ℂ (fun w=> f w*J w) U:=
      ⟨(q.differentiableOn.mono inter_subset_left).mul (A.differentiableOn.mono (subset_univ _)),
       c.mul (A.continuousOn.mono (subset_univ _))⟩
    have P:‖f z*J z‖≤C:=by
       refine Complex.norm_le_of_forall_mem_frontier_norm_le b B ?_ (subset_closure e)
       intro w v
       rw [o.frontier_eq] at v
       have wc:= g v.1
       have m:0 ≤ w.im:=wc.1
       have h0:‖w‖≤r:=by simpa [mem_closedBall] using wc.2
       rw [norm_mul]
       apply le_trans _ (k _ v.1)
       rcases m.eq_or_lt with i|i

       · have h':(w.re:ℂ)=w:=Complex.ext (ofReal_re _) ((ofReal_im _).trans i)
         simp [show f w=0 from h' ▸ u _ ((Complex.abs_re_le_norm w).trans h0)]
       have d:r≤‖w‖:=le_of_not_gt (fun ht=>v.2 ⟨i,mem_ball_zero_iff.mpr ht⟩)
       have H:=Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos u'.le (hpow w (le_antisymm h0 d) i.le))
       simp only [J,Complex.norm_exp,mul_re,ofReal_im,ofReal_re,zero_mul,sub_zero]
       exact mul_le_of_le_one_right (norm_nonneg _) H
    simpa only [norm_mul,J,Complex.norm_exp,mul_re,ofReal_im,ofReal_re,zero_mul,sub_zero] using P
 let W:= U ∩ {z:ℂ|0<(F z).re}
 have D(z:ℂ)(h:z∈W): f z=0:=by
    by_contra H
    let y:=‖f z‖; have y':0<y:=norm_pos_iff.mpr H
    have w:0 < (F z).re:= h.2
    let e:=C/y
    have e':0 ≤ e:=div_nonneg (y'.le.trans (k _ (subset_closure (show z∈U from h.1)))) y'.le
    let t:=(e+1)/(F z).re
    have a: e+1=t*(F z).re:= (div_mul_cancel₀ _ w.ne').symm
    have n:=l t (div_pos (by linarith) w) z h.1
    have m:e<Real.exp (t*(F z).re):= lt_of_lt_of_le (by linarith only [a]) (Real.add_one_le_exp _)
    exact n.not_gt (by rw [mul_comm]; exact (div_lt_iff₀ y').mp m)

 let d:=r/2
 let w:=(d:ℂ)*I
 have hW:w∈W:=by
    have v:0<d:=half_pos p
    have s:0<w.im:=by simp [w,v]
    have t:w∈ ball 0 r:=mem_ball_zero_iff.mpr (by simpa [w,d,norm_real,abs_of_pos p] using half_lt_self p)
    suffices 0<(F w).re from ⟨⟨s,t⟩,this⟩
    simp only [F,w,d,mul_re,mul_im,I_im,I_re,add_re,sub_re,ofReal_re,ofReal_im]
    nlinarith [mul_pos p p]
 have t:IsOpen W:=o.inter (isOpen_lt continuous_const
      (Complex.continuous_re.comp (continuousOn_univ.mp a.continuousOn)))
 have Y:= q.eqOn_of_preconnected_of_eventuallyEq
    (g:=fun _=>0) analyticOnNhd_const (convex_halfSpace_im_gt _).isPreconnected hW.1.1
    (Eventually.mono (t.eventually_mem hW) D)
 exact fun _ h=> Y h

end YM.Velour
